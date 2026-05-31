"""
cbmc_builder.py — Top-level builder for CBMC C file generation.

Mirrors PromelaBuilder: three with_*() setters, one build() → Result[str, Error].

The generated C file has this structure:
  1. File header
  2. #include <stdbool.h>, nondet_int() declaration
  3. State #defines (consts, enum values)
  4. BOUND #define
  5. CWP state #defines  (from CwpCbmcVisitor)
  6. Transition #defines (from BpmnCbmcVisitor)
  7. update_cwp_state()  (from CwpCbmcVisitor)
  8. int main()          (from BpmnCbmcVisitor)
"""

from collections import deque

from returns.result import Failure, Result, Success

from bpmncwpverify.core.bpmn import (
    Bpmn,
    EndEvent,
    ExclusiveGatewayNode,
    Node,
    ParallelGatewayNode,
)
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.error import CbmcGeneratorError, Error, NotInitializedError
from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.bpmn_cbmc_visitor import BpmnCbmcVisitor
from bpmncwpverify.visitors.cwp_cbmc_visitor import CwpCbmcVisitor

# ── R5a bound computation ──────────────────────────────────────────────────────


def _acyclic_depth(node: Node, path: frozenset[str]) -> int:
    """
    Longest path (transition firings) from node to any end event in the acyclic skeleton.
    Back-edges (target already in path) are treated as dead ends (-1).
    XOR gateway: min of valid outgoing branches (each flow = 1 step).
    AND-fork: 1 + sum of all outgoing branches.
    Sequential: 1 + max valid continuation.
    Returns -1 if no end event is reachable without a back-edge.
    """
    if node.id in path:
        return -1
    new_path = path | {node.id}
    if isinstance(node, EndEvent):
        return 1
    if not node.out_flows:
        return -1
    child_depths = [_acyclic_depth(f.target_node, new_path) for f in node.out_flows]
    valid = [d for d in child_depths if d >= 0]
    if not valid:
        return -1
    if isinstance(node, ExclusiveGatewayNode):
        return min(1 + d for d in valid)
    if isinstance(node, ParallelGatewayNode) and node.is_fork:
        return 1 + sum(valid)
    return 1 + max(valid)


def _find_back_edges(
    node: Node,
    gray: set[str],
    black: set[str],
    back_edges: list[tuple[str, str]],
) -> None:
    """DFS coloring to collect back-edges as (source_id, target_id) pairs."""
    if node.id in black or node.id in gray:
        return
    gray.add(node.id)
    for flow in node.out_flows:
        t = flow.target_node
        if t.id in gray:
            back_edges.append((node.id, t.id))
        elif t.id not in black:
            _find_back_edges(t, gray, black, back_edges)
    gray.discard(node.id)
    black.add(node.id)


def _cycle_length_bfs(target: Node, source_id: str) -> int:
    """
    BFS from target to source_id in the forward graph.
    Returns the number of transitions in the cycle (each node = 1 step).
    """
    queue: deque[tuple[Node, int]] = deque([(target, 1)])
    visited: set[str] = {target.id}
    while queue:
        node, dist = queue.popleft()
        if node.id == source_id:
            return dist
        for flow in node.out_flows:
            t = flow.target_node
            if t.id not in visited:
                visited.add(t.id)
                queue.append((t, dist + 1))
    return 2  # fallback: minimum cycle


def _r5a_bound(bpmn: Bpmn, max_retries: int) -> int:
    """
    R5a: acyclic-skeleton longest path + loop contributions, summed across all pools.

    For each process: compute acyclic depth from its start event(s), detect back-edges,
    group by loop-entry node, take the longest cycle per entry, multiply by max_retries.
    """
    total = 0
    for process in bpmn.processes.values():
        for start in process.get_start_states().values():
            acyclic = max(_acyclic_depth(start, frozenset()), 0)

            back_edges: list[tuple[str, str]] = []
            _find_back_edges(start, set(), set(), back_edges)

            node_map: dict[str, Node] = dict(process.all_items())

            # Per loop-entry (back-edge target): keep the longest cycle length.
            target_max_cycle: dict[str, int] = {}
            for source_id, target_id in back_edges:
                if target_id not in node_map:
                    continue
                cycle_len = _cycle_length_bfs(node_map[target_id], source_id)
                prev = target_max_cycle.get(target_id, 0)
                target_max_cycle[target_id] = max(prev, cycle_len)

            loop_total = sum(c * max_retries for c in target_max_cycle.values())
            total += acyclic + loop_total

    return max(total, 1)


# ── State-to-C helpers ────────────────────────────────────────────────────────


def _state_defines(state: State) -> str:
    """
    Emit C #define lines for consts and enum values.

    Consts:     #define <id>  <init_value>
    Enum vals:  #define <value>  N   (sequential per enum, 0-based)
    """
    lines: list[str] = []
    for const in state.consts:
        lines.append(f"#define {const.id:<28} {const.init.value}")
    for enum in state.enums:
        for i, val in enumerate(enum.values):
            lines.append(f"#define {val.value:<28} {i}")
    return "\n".join(lines) + "\n" if lines else ""


def _var_decls(state: State) -> list[str]:
    """
    C variable declarations for main() — bare-bones: all as int.
    e.g. ["int x = 0;"] or ["int terms = TERMS_PENDING;"]
    """
    decls: list[str] = []
    enum_ids = {e.id for e in state.enums}
    for var in state.vars:
        # bare bones: always declare as int regardless of type_
        _ = enum_ids  # noted: ignored in this bare-bones version
        decls.append(f"int {var.id} = {var.init.value};")
    return decls


def _var_params(state: State) -> list[str]:
    """
    C parameter declarations for update_cwp_state() — bare-bones: all int.
    e.g. ["int x"] or ["int terms", "int paymentOffered", ...]
    """
    return [f"int {var.id}" for var in state.vars]


def _var_args(state: State) -> list[str]:
    """
    Call arguments for update_cwp_state() — just variable names.
    e.g. ["x"] or ["terms", "paymentOffered", ...]
    """
    return [var.id for var in state.vars]


# ── C file assembly ────────────────────────────────────────────────────────────


def _generate_c(
    state: State, cwp: Cwp, bpmn: Bpmn, max_retries: int
) -> Result[str, Error]:
    # ── Run CWP visitor ──
    cwp_visitor = CwpCbmcVisitor()
    cwp.accept(cwp_visitor)

    # ── Run BPMN visitor ──
    bpmn_visitor = BpmnCbmcVisitor()
    bpmn.accept(bpmn_visitor)

    if bpmn_visitor.error is not None:
        return Failure(bpmn_visitor.error)

    if bpmn_visitor.num_transitions == 0:
        return Failure(CbmcGeneratorError("BPMN produced no transitions"))

    # ── Derived values ──
    bound = _r5a_bound(bpmn, max_retries)
    st_defines = _state_defines(state)
    v_decls = _var_decls(state)
    v_params = _var_params(state)
    v_args = _var_args(state)

    initial_cwp = cwp_visitor.initial_cwp_state_define()
    cwp_reached_init = cwp_visitor.cwp_reached_init_expr()
    cwp_define_names = cwp_visitor.reachable_state_define_names()

    # ── Assemble ──
    sections: list[str] = []

    sections.append(
        "/* Auto-generated by cbmc_builder.py — do not edit by hand. */\n"
        "#include <stdbool.h>\n"
        "\n"
        "int nondet_int();\n"
    )

    if st_defines:
        sections.append(st_defines)

    sections.append(f"#define {'BOUND':<28} {bound}\n")

    sections.append(cwp_visitor.generate_state_defines())

    sections.append(bpmn_visitor.generate_transition_defines())

    sections.append(cwp_visitor.generate_update_cwp_state(v_params))

    sections.append(
        bpmn_visitor.generate_main(
            var_decls=v_decls,
            var_args=v_args,
            initial_cwp_state=initial_cwp,
            cwp_num_states_define="CWP_NUM_STATES",
            cwp_reached_init=cwp_reached_init,
            cwp_state_define_names=cwp_define_names,
        )
    )

    return Success("\n".join(sections))


# ── Builder class ──────────────────────────────────────────────────────────────


class CbmcBuilder:
    __slots__ = ["bpmn", "cwp", "state", "max_retries"]

    def __init__(self) -> None:
        self.bpmn: Result[Bpmn, Error] = Failure(
            NotInitializedError("CbmcBuilder.bpmn")
        )
        self.cwp: Result[Cwp, Error] = Failure(NotInitializedError("CbmcBuilder.cwp"))
        self.state: Result[State, Error] = Failure(
            NotInitializedError("CbmcBuilder.state")
        )
        self.max_retries: int = 2

    def with_bpmn(self, bpmn: Bpmn) -> "CbmcBuilder":
        self.bpmn = Success(bpmn)
        return self

    def with_cwp(self, cwp: Cwp) -> "CbmcBuilder":
        self.cwp = Success(cwp)
        return self

    def with_state(self, state: State) -> "CbmcBuilder":
        self.state = Success(state)
        return self

    def with_max_retries(self, max_retries: int) -> "CbmcBuilder":
        self.max_retries = max_retries
        return self

    def build(self) -> Result[str, Error]:
        max_retries = self.max_retries
        result: Result[str, Error] = self.state.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda state: self.cwp.bind(  # pyright: ignore[reportUnknownMemberType]
                lambda cwp: self.bpmn.bind(  # pyright: ignore[reportUnknownMemberType]
                    lambda bpmn: _generate_c(state, cwp, bpmn, max_retries)
                )
            )
        )
        return result
