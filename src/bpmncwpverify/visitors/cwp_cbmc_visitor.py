"""
cwp_cbmc_visitor.py — CWP traversal for CBMC C generation.

Collects CWP state and edge data, then emits two C sections:
  1. CWP state #define constants
  2. update_cwp_state() function — flat if/else if state transition + P1 assertion

Only states with in_edges are tracked (mirrors Promela's list_of_cwp_states).
The CWP source node (no in_edges) is collected for its outgoing-edge expressions
but is never assigned a state ID or included in P1 checks.
"""

from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState, CwpVisitor


class CwpCbmcVisitor(CwpVisitor):
    __slots__ = [
        "_states",  # list[CwpState] tracked states (with in_edges), DFS order
        "_edges",  # dict[str, CwpEdge] all edges, keyed by edge.id
        "_visited_ids",  # set[str] visited state IDs — prevents double-visit
        "_init_state",  # CwpState | None — first tracked state (dest of start_state)
    ]

    def __init__(self) -> None:
        self._states: list[CwpState] = []
        self._edges: dict[str, CwpEdge] = {}
        self._visited_ids: set[str] = set()
        self._init_state: CwpState | None = None

    # ── CwpVisitor callbacks ────────────────────────────────────────────────

    def visit_cwp(self, model: Cwp) -> bool:
        # The initial tracking state is the dest of the start_state's first out_edge.
        if model.start_state.out_edges:
            self._init_state = model.start_state.out_edges[0].dest
        return True

    def visit_state(self, state: CwpState) -> bool:
        if state.id in self._visited_ids:
            return False
        self._visited_ids.add(state.id)

        if state.in_edges:
            self._states.append(state)

        # Collect all edges touching this state (deduplicated by ID).
        for edge in state.in_edges + state.out_edges:
            if edge.id not in self._edges:
                self._edges[edge.id] = edge

        return True

    def visit_edge(self, edge: CwpEdge) -> bool:
        return True

    # ── Public properties ───────────────────────────────────────────────────

    @property
    def num_states(self) -> int:
        return len(self._states)

    def state_define_names(self) -> list[str]:
        """Public accessor: ordered list of CWP state #define names."""
        return [self._define_name(s) for s in self._states]

    # ── Name helpers ────────────────────────────────────────────────────────

    def _define_name(self, state: CwpState) -> str:
        """C #define name: CWP_<UPPERCASED_STATE_NAME>"""
        return f"CWP_{state.name.upper()}"

    def _edge_cond_var(self, edge: CwpEdge) -> str:
        """Local bool variable name for an edge condition expression."""
        src = edge.source.name if edge.source else "UNKNOWN"
        dst = edge.dest.name
        return f"e_{src}_to_{dst}"

    def _mapping_function(self, state: CwpState) -> str:
        """
        C boolean expression: true when the CWP is in this state.
        Logic: (AND of in-edge conditions) && !(OR of out-edge conditions)
        Mirrors CwpPromelaVisitor._build_mapping_function().
        """
        in_part = (
            " && ".join(self._edge_cond_var(e) for e in state.in_edges)
            if state.in_edges
            else "true"
        )
        out_part = (
            " || ".join(self._edge_cond_var(e) for e in state.out_edges)
            if state.out_edges
            else "false"
        )
        return f"({in_part}) && !({out_part})"

    # ── Code-generation methods ─────────────────────────────────────────────

    def initial_cwp_state_define(self) -> str:
        """Returns the #define name of the initial CWP tracking state."""
        if self._init_state is not None and self._init_state in self._states:
            return self._define_name(self._init_state)
        if self._states:
            return self._define_name(self._states[0])
        return "0"

    def cwp_reached_init_expr(self) -> str:
        """
        C initializer for cwp_reached[].
        Only the initial tracking state (dest of start_state's first out-edge) starts
        as reached; the CWP start_state itself is never actually entered by the model
        (its mapping function is always false at runtime).
        """
        values = ["false"] * len(self._states)
        if self._init_state is not None and self._init_state in self._states:
            values[self._states.index(self._init_state)] = "true"
        return "{" + ", ".join(values) + "}"

    def generate_state_defines(self) -> str:
        """Emit: #define CWP_<NAME> N  for each tracked state, plus CWP_NUM_STATES."""
        lines = [
            "/* ── CWP state IDs ─────────────────────────────────────────────────────── */"
        ]
        for i, state in enumerate(self._states):
            lines.append(f"#define {self._define_name(state):<28} {i}")
        lines.append(f"#define {'CWP_NUM_STATES':<28} {len(self._states)}")
        return "\n".join(lines) + "\n"

    def generate_update_cwp_state(self, var_params: list[str]) -> str:
        """
        Emit the update_cwp_state() C function.

        var_params: list of C parameter declarations for the data variables,
                    e.g. ["int x"] or ["int terms", "int paymentOffered", ...].
        """
        lines: list[str] = []

        # ── signature ──
        params = ", ".join(["int *cwp_state", "bool cwp_reached[]"] + var_params)
        lines.append("/* out: cwp_state, cwp_reached */")
        lines.append(f"static void update_cwp_state({params})")
        lines.append("{")
        lines.append("    int old_state = *cwp_state;")
        lines.append("")

        # ── edge condition booleans ──
        lines.append("    /* CWP edge conditions */")
        emitted_edges: set[str] = set()
        for edge in self._edges.values():
            if edge.id not in emitted_edges and edge.expression:
                emitted_edges.add(edge.id)
                var = self._edge_cond_var(edge)
                lines.append(f"    bool {var} = ({edge.expression});")
        lines.append("")

        # ── next-state booleans (mapping function per tracked state) ──
        lines.append("    /* Next state: mapping function per CWP state */")
        for state in self._states:
            mapping = self._mapping_function(state)
            lines.append(f"    bool next_{state.name} = {mapping};")
        lines.append("")

        # ── priority ternary: terminal states first (no out_edges) ──
        terminals = [s for s in self._states if not s.out_edges]
        non_terminals = [s for s in self._states if s.out_edges]
        priority_order = terminals + non_terminals

        if priority_order:
            # Build the chained ternary, one state per line.
            ternary_parts = [
                f"next_{s.name} ? {self._define_name(s)}" for s in priority_order
            ]
            # Last fallback: stay in current state.
            indent = " " * 20
            chain = f"\n{indent}: ".join(ternary_parts)
            chain += f"\n{indent}: old_state;"
            lines.append(f"    int new_state = {chain}")
        else:
            lines.append("    int new_state = old_state;")
        lines.append("")

        # ── P1: valid transition assertion ──
        lines.append(
            "    /* P1: transition follows a valid CWP edge (or stays in same state) */"
        )
        p1_cases: list[str] = []
        # Self-loops for every tracked state.
        for state in self._states:
            dn = self._define_name(state)
            p1_cases.append(f"(old_state == {dn} && new_state == {dn})")
        # Forward edges whose source is a tracked state (has in_edges).
        for edge in self._edges.values():
            if edge.source and edge.source.in_edges:
                src_dn = self._define_name(edge.source)
                dst_dn = self._define_name(edge.dest)
                if src_dn != dst_dn:
                    p1_cases.append(f"(old_state == {src_dn} && new_state == {dst_dn})")
        p1_expr = " ||\n        ".join(p1_cases)
        lines.append("    __CPROVER_assert(")
        lines.append(f"        {p1_expr},")
        lines.append('        "CWP P1: transition follows valid CWP edge");')
        lines.append("")

        # ── commit ──
        lines.append("    /* Commit */")
        lines.append("    *cwp_state             = new_state;")
        lines.append("    cwp_reached[new_state] = true;")
        lines.append("}")

        return "\n".join(lines) + "\n"
