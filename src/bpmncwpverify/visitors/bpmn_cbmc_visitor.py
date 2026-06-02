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
from bpmncwpverify.core.error import Error


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

    # Matches: :: GUARD -> VAR = VALUE  (any guard, single line)
    _ASSIGN_BRANCH_RE = re.compile(r"::\s*(.+?)\s*->\s*(\w+)\s*=\s*(\S+)\s*$")

    @staticmethod
    def _join_continuation_lines(lines: list[str]) -> list[str]:
        """Join ':: GUARD ->' lines with the statement on the following line.

        Promela allows a branch guard and its statement on separate lines:
            :: trndSevNeed == outsideHomeCare ->
                sevNeed = expired
        This pass merges them into one line so _translate_behavior can parse them
        with a single regex. Lines that continue to a nested 'if' or another '::'
        are left as-is (can't be expressed as a single VAR = VALUE assignment).
        """
        result: list[str] = []
        i = 0
        while i < len(lines):
            stripped = lines[i].strip()
            if stripped.startswith("::") and stripped.endswith("->"):
                # Skip blank lines then look at the next non-empty line.
                i += 1
                while i < len(lines) and not lines[i].strip():
                    i += 1
                if i < len(lines):
                    next_s = lines[i].strip()
                    # Only join if the continuation is a plain statement, not
                    # another branch delimiter or a nested if/fi keyword.
                    if not next_s.startswith("::") and next_s not in ("if", "fi"):
                        stripped = stripped + " " + next_s
                        i += 1
            else:
                i += 1
            result.append(stripped)
        return result

    @staticmethod
    def _translate_behavior_impl(behavior: str) -> tuple[list[str], bool]:
        """Internal implementation of behavior translation.

        Returns (lines, always_assigns) where always_assigns is True if every
        execution path through the behavior is guaranteed to assign to at least
        one state variable (i.e., the behavior contains at least one plain
        statement or a Case-A if/fi block — no Case-B no-op-branch-only blocks).

        Handles three forms of Promela if/fi branches:
          :: true -> VAR = VALUE          (unconditional assignment)
          :: COND -> VAR = VALUE          (conditional assignment)
          :: COND  or  :: true            (no-op / skip branch)

        Case A — all branches assign the same variable, no no-ops (always_assigns):
            int t = nondet_int();
            __CPROVER_assume(t == A || (t == B && (COND)));
            var = t;

        Case B — mixed branches (no-op or multiple variables, NOT always_assigns
                  unless mixed with plain statements or Case-A blocks elsewhere):
            int t = nondet_int();
            __CPROVER_assume(t == 0 || (t == 1 && (COND)) || t == 2);
            if (t == 0) { var = A; }
            else if (t == 1) { var = B; }
            // t == 2: no-op branch

        Plain statements are passed through with a semicolon added if missing.
        Stray 'fi' tokens from nested blocks are silently skipped.
        Empty behavior returns ([], False).
        """
        behavior = behavior.strip()
        if not behavior:
            return [], False

        result: list[str] = []
        # Counter for temp-var naming: t, t1, t2, ... (one per if/fi block).
        iffi_idx = 0
        # True once we see any guaranteed-executing assignment.
        always_assigns = False

        raw_lines = BpmnCbmcVisitor._join_continuation_lines(behavior.splitlines())
        i = 0
        while i < len(raw_lines):
            line = raw_lines[i].strip()

            if line == "if":
                # Collect branches until the first 'fi'.
                # Each branch is (guard, var, val) where var/val are None for no-ops.
                branches: list[tuple[str, str | None, str | None]] = []
                i += 1
                while i < len(raw_lines) and raw_lines[i].strip() != "fi":
                    bline = raw_lines[i].strip()
                    m = BpmnCbmcVisitor._ASSIGN_BRANCH_RE.match(bline)
                    if m:
                        guard, var, val = m.group(1).strip(), m.group(2), m.group(3)
                        branches.append((guard, var, val))
                    elif bline.startswith("::"):
                        # No-op branch: :: GUARD (no assignment after ->).
                        guard_part = bline[2:].strip()
                        if guard_part.endswith("->"):
                            guard_part = guard_part[:-2].strip()
                        # Promela 'else' is not valid C; treat as always-enabled.
                        guard = "true" if guard_part in ("else", "") else guard_part
                        branches.append((guard, None, None))
                    i += 1
                i += 1  # skip 'fi'

                if not branches:
                    continue

                assign_branches = [
                    (g, v, val) for g, v, val in branches if v is not None
                ]
                noop_guards = [g for g, v, _ in branches if v is None]
                vars_used = list(dict.fromkeys(v for _, v, _ in assign_branches))

                t_var = "t" if iffi_idx == 0 else f"t{iffi_idx}"
                iffi_idx += 1

                if assign_branches and len(vars_used) == 1 and not noop_guards:
                    # Case A: all same variable, no no-ops → always assigns.
                    always_assigns = True
                    var = vars_used[0]
                    assume_parts: list[str] = []
                    for guard, _, val in assign_branches:
                        if guard == "true":
                            assume_parts.append(f"{t_var} == {val}")
                        else:
                            assume_parts.append(f"({t_var} == {val} && ({guard}))")
                    result.append(f"int {t_var} = nondet_int();")
                    result.append(f"__CPROVER_assume({' || '.join(assume_parts)});")
                    result.append(f"{var} = {t_var};")

                elif assign_branches:
                    # Case B: mixed or multi-variable → per-branch index.
                    # Does NOT set always_assigns (no-op path may execute).
                    assume_parts = []
                    for idx, (guard, _, _) in enumerate(assign_branches):
                        if guard == "true":
                            assume_parts.append(f"{t_var} == {idx}")
                        else:
                            assume_parts.append(f"({t_var} == {idx} && ({guard}))")
                    for j, guard in enumerate(noop_guards):
                        noop_idx = len(assign_branches) + j
                        if guard == "true":
                            assume_parts.append(f"{t_var} == {noop_idx}")
                        else:
                            assume_parts.append(f"({t_var} == {noop_idx} && ({guard}))")
                    result.append(f"int {t_var} = nondet_int();")
                    result.append(f"__CPROVER_assume({' || '.join(assume_parts)});")
                    for idx, (_, var, val) in enumerate(assign_branches):
                        kw = "if" if idx == 0 else "else if"
                        result.append(f"{kw} ({t_var} == {idx}) {{ {var} = {val}; }}")
                # else: only no-op branches — nothing to emit.

            elif line == "fi":
                # Stray 'fi' from a nested if/fi whose inner 'fi' already closed
                # the translator's scan loop — skip it silently.
                i += 1

            elif line:
                # Plain statement — always executes → guarantees an assignment.
                always_assigns = True
                stmt = line if line.endswith(";") else line + ";"
                result.append(stmt)
                i += 1

            else:
                i += 1

        return result, always_assigns

    @staticmethod
    def _translate_behavior(behavior: str) -> list[str]:
        """Public API: translate behavior to C lines.

        Thin wrapper around _translate_behavior_impl; discards the always_assigns
        flag so callers that don't need it (e.g., tests) get a plain list[str].
        Use _translate_behavior_impl directly when the flag is needed.
        """
        lines, _ = BpmnCbmcVisitor._translate_behavior_impl(behavior)
        return lines

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
        if event.id in self._visited_ids:
            return False
        self._visited_ids.add(event.id)
        self._transitions.append((event, None))
        return True

    # ── public properties ──────────────────────────────────────────────────────

    @property
    def num_transitions(self) -> int:
        return len(self._transitions)

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
        cwp_num_states_define: str,
        cwp_state_define_names: list[str],
    ) -> str:
        """
        Emit the complete int main() function.

        var_decls:             C declarations for the shared data variables,
                               e.g. ["int x = 0;"].
        var_args:              Call arguments for update_cwp_state(),
                               e.g. ["x"].
        cwp_num_states_define: #define name for the CWP state count,
                               e.g. "CWP_NUM_STATES".
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
        lines.append("    int cwp_state = 0;")
        lines.append(f"    bool cwp_reached[{cwp_num_states_define}] = {{false}};")
        # Compute initial CWP state from initial variable values.
        # update_cwp_state transitions from state 0 (the CWP start_state) to
        # whichever state the initial variable values map to, or stays in 0.
        # P1 passes because 0→0 (self-loop) and 0→dest (start_state out_edge) are
        # both valid CWP edges.
        args = ", ".join(["&cwp_state", "cwp_reached"] + var_args)
        lines.append(f"    update_cwp_state({args});")
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
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            translated, always_assigns = self._translate_behavior_impl(node.behavior)
            for stmt in translated:
                lines.append(f"            {stmt}")
            for f in node.out_flows:
                lines.append(f"            {self._flow_place_name(f)} = true;")
            if always_assigns:
                args = ", ".join(["&cwp_state", "cwp_reached"] + var_args)
                lines.append(f"            update_cwp_state({args});")

        elif isinstance(node, ExclusiveGatewayNode):
            assert flow is not None
            # Consume all gateway incoming places (OR-merge: clear all).
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            # Produce the selected outgoing place.
            lines.append(f"            {self._flow_place_name(flow)} = true;")

        elif isinstance(node, IntermediateEvent):
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            for f in node.out_flows:
                lines.append(f"            {self._flow_place_name(f)} = true;")

        elif isinstance(node, ParallelGatewayNode):
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            for f in node.out_flows:
                lines.append(f"            {self._flow_place_name(f)} = true;")

        elif isinstance(node, EndEvent):
            # Consume all incoming places.
            for f in node.in_flows:
                lines.append(f"            {self._flow_place_name(f)} = false;")
            lines.append(f"            {node.id}_reached = true;")
            lines.append("            running = false;")

        return lines
