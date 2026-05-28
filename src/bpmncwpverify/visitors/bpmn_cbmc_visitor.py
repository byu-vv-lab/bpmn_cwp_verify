"""
bpmn_cbmc_visitor.py — BPMN traversal for CBMC C generation.

Collects BPMN place and transition data via DFS, then emits:
  1. Transition #define constants
  2. int main() — token places, enable conditions, __CPROVER_assume,
     if/else if dispatch, reachability block

Bare-bones scope (v1): handles plain start events, tasks, XOR gateways
(one T_ per outgoing flow), and end events.  Parallel gateways and
intermediate events set self.error and halt further traversal.

Place naming:
  - Start event's own token:   p_<event.id>              (initialized true)
  - Sequence-flow edge place:  p_<target.id>_FROM_<source.id>  (initialized false)

Transition naming:
  - Start/task/end node:       T_<node.id>
  - XOR gateway outgoing flow: T_<flow.id>
"""

import re

from bpmncwpverify.core.bpmn import (
    BpmnVisitor,
    EndEvent,
    ExclusiveGatewayNode,
    IntermediateEvent,
    Node,
    ParallelGatewayNode,
    SequenceFlow,
    StartEvent,
    Task,
)
from bpmncwpverify.core.error import CbmcUnsupportedElementError, Error


class BpmnCbmcVisitor(BpmnVisitor):
    __slots__ = [
        "_transitions",  # list[tuple[Node, SequenceFlow | None]]
        "_places",  # dict[str, bool] — place_name → initial bool value
        "_end_event_ids",  # list[str] — end event node IDs, for reachability block
        "_visited_ids",  # set[str] — DFS pruning
        "error",  # Error | None
    ]

    def __init__(self) -> None:
        self._transitions: list[tuple[Node, SequenceFlow | None]] = []
        self._places: dict[str, bool] = {}
        self._end_event_ids: list[str] = []
        self._visited_ids: set[str] = set()
        self.error: Error | None = None

    # ── name helpers ─────────────────────────────────────────────────────────

    @staticmethod
    def _flow_place_name(flow: SequenceFlow) -> str:
        """p_<target.id>_FROM_<source.id>"""
        return f"p_{flow.target_node.id}_FROM_{flow.source_node.id}"

    @staticmethod
    def _start_place_name(event: StartEvent) -> str:
        return f"p_{event.id}"

    @staticmethod
    def _transition_define_name(node: Node, flow: "SequenceFlow | None") -> str:
        if flow is not None:
            return f"T_{flow.id}"
        return f"T_{node.id}"

    @staticmethod
    def _enable_var_name(node: Node, flow: "SequenceFlow | None") -> str:
        if flow is not None:
            return f"en_{flow.id}"
        return f"en_{node.id}"

    # ── enable-expression helpers ─────────────────────────────────────────────

    def _in_place_names(self, node: Node) -> list[str]:
        """Place names for all incoming flow edges of a non-start node."""
        return [f"p_{node.id}_FROM_{f.source_node.id}" for f in node.in_flows]

    def _or_of_in_places(self, node: Node) -> str:
        places = self._in_place_names(node)
        if len(places) == 1:
            return places[0]
        return " || ".join(places)

    def _and_of_in_places(self, node: Node) -> str:
        places = self._in_place_names(node)
        if len(places) == 1:
            return places[0]
        return " && ".join(places)

    def _enable_expr(self, node: Node, flow: "SequenceFlow | None") -> str:
        """C boolean expression: true when this transition may fire."""
        if isinstance(node, StartEvent):
            return self._start_place_name(node)
        if isinstance(node, ExclusiveGatewayNode):
            assert flow is not None
            gw_in = self._or_of_in_places(node)
            if flow.expression:
                return f"({gw_in}) && ({flow.expression})"
            return f"({gw_in})"
        if isinstance(node, ParallelGatewayNode):
            # Fork: OR (usually one in_place). Join: AND (all branches must complete).
            if node.is_fork:
                return self._or_of_in_places(node)
            return self._and_of_in_places(node)
        return self._or_of_in_places(node)

    # Matches one branch of a Promela if/fi block:  :: true -> VAR = VALUE
    _BRANCH_RE = re.compile(r"::\s*true\s*->\s*(\w+)\s*=\s*(\S+)")

    @staticmethod
    def _translate_behavior(behavior: str) -> list[str]:
        """Translate BPMN task behavior (Promela if/fi or plain C) to C statements."""
        behavior = behavior.strip()
        if not behavior:
            return []

        result: list[str] = []
        iffi_idx = 0

        raw_lines = behavior.splitlines()
        i = 0
        while i < len(raw_lines):
            line = raw_lines[i].strip()

            if line == "if":
                branches: list[tuple[str, str]] = []
                i += 1
                while i < len(raw_lines) and raw_lines[i].strip() != "fi":
                    m = BpmnCbmcVisitor._BRANCH_RE.match(raw_lines[i].strip())
                    if m:
                        branches.append((m.group(1), m.group(2)))
                    i += 1
                i += 1  # skip 'fi'

                if branches:
                    vars_in_order: list[str] = []
                    for var, _ in branches:
                        if var not in vars_in_order:
                            vars_in_order.append(var)

                    for var in vars_in_order:
                        values = [val for v, val in branches if v == var]
                        t_var = "t" if iffi_idx == 0 else f"t{iffi_idx}"
                        iffi_idx += 1
                        assume = " || ".join(f"{t_var} == {val}" for val in values)
                        result.append(f"int {t_var} = nondet_int();")
                        result.append(f"__CPROVER_assume({assume});")
                        result.append(f"{var} = {t_var};")

            elif line:
                stmt = line if line.endswith(";") else line + ";"
                result.append(stmt)
                i += 1

            else:
                i += 1

        return result

    def visit_start_event(self, event: StartEvent) -> bool:
        if event.id in self._visited_ids:
            return False
        self._visited_ids.add(event.id)
        # Start event's own token place (initialized true)
        self._places[self._start_place_name(event)] = True
        self._transitions.append((event, None))
        return True

    def visit_task(self, task: Task) -> bool:
        if task.id in self._visited_ids:
            return False
        self._visited_ids.add(task.id)
        self._transitions.append((task, None))
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        if gateway.id in self._visited_ids:
            return False
        self._visited_ids.add(gateway.id)
        # One transition per outgoing flow
        for flow in gateway.out_flows:
            self._transitions.append((gateway, flow))
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        if event.id in self._visited_ids:
            return False
        self._visited_ids.add(event.id)
        self._transitions.append((event, None))
        self._end_event_ids.append(event.id)
        return True

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        # Register the place for this edge (all flows, including back-edges)
        place = self._flow_place_name(flow)
        if place not in self._places:
            self._places[place] = False
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        if gateway.id in self._visited_ids:
            return False
        self._visited_ids.add(gateway.id)
        self._transitions.append((gateway, None))
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self.error = CbmcUnsupportedElementError(event.id, "IntermediateEvent")
        return False

    # ── public properties ──────────────────────────────────────────────────────

    @property
    def num_transitions(self) -> int:
        return len(self._transitions)

    def compute_bound(self) -> int:
        """STUB: returns num_transitions × 4 — replace with R5a longest-path algorithm.

        An undersized bound causes silent false confidence (CBMC reports
        VERIFICATION SUCCESSFUL without exploring all paths).
        R5a longest-path algorithm (see cbmc_generator_requirements.md).
        """
        return self.num_transitions * 4

    # ── code generation ────────────────────────────────────────────────────────

    def generate_transition_defines(self) -> str:
        """Emit: #define T_<name>  N  for each transition."""
        lines = [
            "/* ── Transition IDs ─────────────────────────────────────────────────────── */"
        ]
        for i, (node, flow) in enumerate(self._transitions):
            name = self._transition_define_name(node, flow)
            lines.append(f"#define {name:<36} {i}")
        return "\n".join(lines) + "\n"

    def generate_main(
        self,
        var_decls: list[str],
        var_args: list[str],
        initial_cwp_state: str,
        cwp_num_states_define: str,
        cwp_reached_init: str,
        cwp_state_define_names: list[str],
    ) -> str:
        """
        Emit the complete int main() function.

        var_decls:             C declarations for the shared data variables,
                               e.g. ["int x = 0;"].
        var_args:              Call arguments for update_cwp_state(),
                               e.g. ["x"].
        initial_cwp_state:     #define name of the initial CWP tracking state,
                               e.g. "CWP_INCREMENT_X".
        cwp_num_states_define: #define name for the CWP state count,
                               e.g. "CWP_NUM_STATES".
        cwp_reached_init:      C array initializer for cwp_reached[],
                               e.g. "{true, false}".
        cwp_state_define_names: ordered list of CWP state #define names,
                               e.g. ["CWP_INCREMENT_X", "CWP_END"].
        """
        lines: list[str] = []
        lines.append("int main() {")
        lines.append("")

        # ── shared variable declarations ──
        if var_decls:
            for decl in var_decls:
                lines.append(f"    {decl}")
            lines.append("")

        # ── token places ──
        lines.append(
            "    /* ── Token places — one bool per sequence-flow edge ────────────────── */"
        )
        for place_name, initial in self._places.items():
            val = "true" if initial else "false"
            lines.append(f"    bool {place_name} = {val};")
        lines.append("")

        # ── end-event reachability vars ──
        if self._end_event_ids:
            lines.append("    /* Reachability tracking */")
            for eid in self._end_event_ids:
                lines.append(f"    bool {eid}_reached = false;")
            lines.append("")

        # ── CWP tracking ──
        lines.append(
            "    /* ── CWP state tracking ─────────────────────────────────────────────── */"
        )
        lines.append(f"    int cwp_state = {initial_cwp_state};")
        lines.append(
            f"    bool cwp_reached[{cwp_num_states_define}] = {cwp_reached_init};"
        )
        lines.append("")

        # ── scheduling loop ──
        lines.append("    bool running = true;")
        lines.append("    int step = 0;")
        lines.append("    while (running && step < BOUND) {")
        lines.append("")
        lines.append("        int choice = nondet_int();")
        lines.append("")

        # enable conditions
        lines.append(
            "        /* ── Enable conditions ──────────────────────────────────────────── */"
        )
        for node, flow in self._transitions:
            en_var = self._enable_var_name(node, flow)
            en_expr = self._enable_expr(node, flow)
            lines.append(f"        bool {en_var} = {en_expr};")
        lines.append("")

        # __CPROVER_assume
        assume_parts = [
            f"(choice == {self._transition_define_name(n, f)} && {self._enable_var_name(n, f)})"
            for n, f in self._transitions
        ]
        assume_sep = " ||\n            "
        lines.append("        __CPROVER_assume(")
        lines.append(f"            {assume_sep.join(assume_parts)}")
        lines.append("        );")
        lines.append("")

        # transition bodies
        lines.append(
            "        /* ── Transition bodies ──────────────────────────────────────────── */"
        )
        for idx, (node, flow) in enumerate(self._transitions):
            t_name = self._transition_define_name(node, flow)
            kw = "if" if idx == 0 else "} else if"
            lines.append(f"        {kw} (choice == {t_name}) {{")
            lines.extend(self._transition_body(node, flow, var_args))

        if self._transitions:
            lines.append("        }")
        lines.append("")

        lines.append("        step++;")
        lines.append("    }")
        lines.append("")

        # reachability block
        lines.append("    #ifdef REACHABILITY")
        for eid in self._end_event_ids:
            lines.append(f"        __CPROVER_cover({eid}_reached);")
        for define_name in cwp_state_define_names:
            lines.append(f"        __CPROVER_cover(cwp_reached[{define_name}]);")
        lines.append("    #endif")
        lines.append("")
        lines.append("    return 0;")
        lines.append("}")

        return "\n".join(lines) + "\n"

    def _transition_body(
        self,
        node: Node,
        flow: "SequenceFlow | None",
        var_args: list[str],
    ) -> list[str]:
        """Lines for the body of a single if/else-if branch (no braces)."""
        lines: list[str] = []

        if isinstance(node, StartEvent):
            # Consume own place; produce downstream flow places.
            lines.append(f"            {self._start_place_name(node)} = false;")
            for f in node.out_flows:
                lines.append(f"            {self._flow_place_name(f)} = true;")

        elif isinstance(node, Task):
            # Consume all incoming places (OR-merge: zero every in_flow slot).
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            # Execute behavior statements.
            behavior = node.behavior.strip()
            if behavior:
                for stmt in behavior.splitlines():
                    stmt = stmt.strip()
                    if stmt:
                        if not stmt.endswith(";"):
                            stmt += ";"
                        lines.append(f"            {stmt}")
            # Produce all outgoing flow places.
            for f in node.out_flows:
                lines.append(f"            {self._flow_place_name(f)} = true;")
            # Call update_cwp_state after any state-modifying task.
            if behavior:
                args = ", ".join(["&cwp_state", "cwp_reached"] + var_args)
                lines.append(f"            update_cwp_state({args});")

        elif isinstance(node, ExclusiveGatewayNode):
            assert flow is not None
            # Consume all gateway incoming places (OR-merge: clear all).
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            # Produce the selected outgoing place.
            lines.append(f"            {self._flow_place_name(flow)} = true;")

        elif isinstance(node, EndEvent):
            # Consume all incoming places.
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            lines.append(f"            {node.id}_reached = true;")
            lines.append("            running = false;")

        return lines
