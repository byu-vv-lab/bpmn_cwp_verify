from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Failure, Result, Success

from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.error import (
    CwpEdgeInvalidStateError,
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoParentEdgeError,
    CwpNoStartStateError,
    Error,
    ErrorException,
)
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.cwp_connectivity_visitor import CwpConnectivityVisitor


class CwpBuilder:
    __slots__ = [
        "_cur_edge_letter",
        "_cwp",
        "_pending_edges",
        "_pending_expressions",
        "_pending_start_edge",
    ]

    def __init__(self) -> None:
        self._cur_edge_letter = "A"
        self._cwp = Cwp()
        self._pending_edges: list[tuple[CwpEdge, str, str]] = []
        self._pending_expressions: list[tuple[ExpressionListener, str, str, State]] = []
        self._pending_start_edge: CwpEdge | None = None

    def gen_edge_name(self) -> str:
        ret = "Edge" + self._cur_edge_letter
        self._cur_edge_letter = chr(ord(self._cur_edge_letter) + 1)
        return ret

    def build(self) -> Result[Cwp, Error]:
        try:
            for edge, source_ref, target_ref in self._pending_edges:
                self._with_edge(edge, source_ref, target_ref)

            self._find_start_state()
            # this should only ever fail if the caller forgot to call with_start_edge()
            if self._pending_start_edge is None:
                return Failure(CwpNoStartStateError())
            self._with_start_edge(self._pending_start_edge)

            for expr_checker, expression, parent, state in self._pending_expressions:
                self._check_expression(expr_checker, expression, parent, state)

            end_states = [
                state
                for state in self._cwp.states.values()
                if not state.out_edges and state.in_edges
            ]

            if not end_states:
                return Failure(CwpNoEndStatesError())

            # This step ensures connectivity of the graph and sets leaf edges
            visitor = CwpConnectivityVisitor()
            self._cwp.accept(visitor)

            return Success(self._cwp)
        except ErrorException as e:
            return Failure(e.error)

    def with_edge(
        self, edge: CwpEdge, source_ref: str, target_ref: str
    ) -> "CwpBuilder":
        self._pending_edges.append((edge, source_ref, target_ref))
        return self

    def check_expression(
        self,
        expr_checker: ExpressionListener,
        expression: str,
        parent: str,
        state: State,
    ) -> None:
        self._pending_expressions.append((expr_checker, expression, parent, state))

    def with_state(self, cwpState: CwpState) -> "CwpBuilder":
        self._cwp.states[cwpState.id] = cwpState
        return self

    def with_start_edge(self, edge: CwpEdge) -> "CwpBuilder":
        self._pending_start_edge = edge
        return self

    def _with_start_edge(self, edge: CwpEdge) -> None:
        dest = self._cwp.states[self._cwp.start_state.id]
        dest.in_edges.append(edge)
        edge.set_dest(dest)
        self._cwp.edges[edge.id] = edge

    def _with_edge(self, edge: CwpEdge, source_ref: str, target_ref: str) -> None:
        if source_ref not in self._cwp.states or target_ref not in self._cwp.states:
            raise ErrorException(CwpEdgeInvalidStateError(edge.id))
        source = self._cwp.states[source_ref]
        source.out_edges.append(edge)
        edge.set_source(source)

        dest = self._cwp.states[target_ref]
        dest.in_edges.append(edge)
        edge.set_dest(dest)
        self._cwp.edges[edge.id] = edge

    def _check_expression(
        self,
        expr_checker: ExpressionListener,
        expression: str,
        parent: str,
        state: State,
    ) -> None:
        edge = self._cwp.edges.get(parent)
        if not edge:
            raise ErrorException(CwpNoParentEdgeError(parent))
        expr: str = CwpEdge.cleanup_expression(expression)
        edge.expression = CwpEdge.build_ast(expr)
        result = edge.expression.type_check(state)
        if not_(is_successful)(result):
            raise ErrorException(result.failure())

    def _find_start_state(self) -> None:
        found: bool = False
        start_states: list[CwpState] = []

        for cwpState in self._cwp.states.values():
            if not cwpState.in_edges and cwpState.out_edges:
                if found:
                    start_states.append(cwpState)
                self._cwp.start_state = cwpState
                self._cwp.start_state.init_state = True
                found = True

        if not found:
            raise ErrorException(CwpNoStartStateError())
        elif start_states:
            raise ErrorException(
                CwpMultStartStateError([state.id for state in start_states])
            )
