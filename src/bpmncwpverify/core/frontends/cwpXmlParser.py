from xml.etree.ElementTree import Element

from returns.pipeline import is_successful
from returns.result import Failure, Result, Success

from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.error import (
    CwpEdgeNoExpressionError,
    CwpEdgeNoParentError,
    CwpEdgeNoStateError,
    CwpFileStructureError,
    CwpUnsupportedElementError,
    Error,
    ErrorException,
)
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.cwp_graph_visitor import CwpGraphVizVisitor


class CwpXmlParser:
    def _get_mx_cells(self, root: Element) -> list[Element]:
        if (diagram := root.find("diagram")) is None:
            raise ErrorException(CwpFileStructureError("diagram"))
            raise ErrorException(CwpFileStructureError("diagram"))
        if (mx_graph_model := diagram.find("mxGraphModel")) is None:
            raise ErrorException(CwpFileStructureError("mxGraphModel"))
            raise ErrorException(CwpFileStructureError("mxGraphModel"))
        if (mx_root := mx_graph_model.find("root")) is None:
            raise ErrorException(CwpFileStructureError("root"))
            raise ErrorException(CwpFileStructureError("root"))
        if not (mx_cells := mx_root.findall("mxCell")):
            raise ErrorException(CwpFileStructureError("mxCell"))
            raise ErrorException(CwpFileStructureError("mxCell"))
        if object := mx_root.findall("object"):
            raise ErrorException(CwpUnsupportedElementError(len(object), "object"))
            raise ErrorException(CwpUnsupportedElementError(len(object), "object"))
        return mx_cells

    def _get_all_items(self, mx_cells: list[Element]) -> list[Element]:
        return [itm for itm in mx_cells]

    def _get_edges(self, mx_cells: list[Element]) -> list[Element]:
        return [itm for itm in mx_cells if itm.get("edge")]

    def _get_states(self, mx_cells: list[Element]) -> list[Element]:
        return [itm for itm in mx_cells if itm.get("vertex")]

    def _get_edge_labels(self, all_items: list[Element]) -> dict[str, str]:
        """Maps an edge's mxCell id -> its label's expression text, for every
        edgeLabel item that has a parent and a value."""
        labels: dict[str, str] = {}
        for itm in all_items:
            style = itm.get("style")
            if style and "edgeLabel" in style:
                parent = itm.get("parent")
                expression = itm.get("value")
                if not parent:
                    raise ErrorException(CwpEdgeNoParentError(itm))
                if not expression:
                    raise ErrorException(CwpEdgeNoExpressionError(itm))
                labels[parent] = expression
        return labels

    def _add_states(self, builder: CwpBuilder, states: list[Element]) -> None:
        unsupported_shapes: int = 0
        for element in states:
            style = element.get("style")
            if style and "edgeLabel" not in style:
                if "rounded=1" not in style and "rounded=0" not in style:
                    unsupported_shapes += 1
                state = CwpState.from_xml(element)
                builder = builder.with_state(state)

        if unsupported_shapes != 0:
            raise ErrorException(
                CwpUnsupportedElementError(
                    unsupported_shapes, "different shapes other than rectangles"
                )
            )

    def _apply_initial_values(
        self, state: State, initial_values: list[tuple[str, str | list[str]]]
    ) -> Result[None, Error]:
        for name, value in initial_values:
            if isinstance(value, list):
                result = state.set_array_value(name, value)
            else:
                result = state.set_variable_value(name, value)
            if not isinstance(result, Success):
                return Failure(result.failure())
        return Success(None)

    def _build_start_edge(
        self,
        builder: CwpBuilder,
        element: Element,
        edge_labels: dict[str, str],
        state: State,
        target_ref: str,
    ) -> str:
        """Builds the start edge ([*] --> target) from an mxCell with a
        target but no source, applying any initial-value expression to
        state. Returns the edge's mxCell id so callers can exclude it from
        further expression type-checking."""
        edge_id: str | None = element.get("id")
        if edge_id is None:
            raise ErrorException(CwpEdgeNoStateError(element))

        edge = CwpEdge.from_mmd(target_ref, builder.gen_edge_name())

        raw_expr = edge_labels.get(edge_id)
        if raw_expr is not None:
            expr: str = CwpEdge.cleanup_expression(raw_expr)
            edge.expression = CwpEdge.build_ast(expr)
            result = edge.parse_initial_values().bind(  # pyright: ignore[reportUnknownMemberType]
                lambda values: self._apply_initial_values(state, values)
            )
            if not isinstance(result, Success):
                raise ErrorException(result.failure())

        all_variables_assigned = state.assert_all_values_set()
        if not is_successful(all_variables_assigned):
            raise ErrorException(all_variables_assigned.failure())

        builder.with_start_edge(edge)
        return edge_id

    def _add_edges(
        self,
        builder: CwpBuilder,
        edges: list[Element],
        edge_labels: dict[str, str],
        state: State,
    ) -> str | None:
        """Adds all normal edges to the builder, and builds the start edge
        (if present) separately. Returns the start edge's mxCell id, if
        there was one, so it can be excluded from expression type-checking."""
        start_edge_id: str | None = None

        for element in edges:
            source_ref = element.get("source")
            target_ref = element.get("target")

            if not target_ref:
                raise ErrorException(CwpEdgeNoStateError(element))

            if not source_ref:
                if start_edge_id is not None:
                    raise ErrorException(CwpEdgeNoStateError(element))
                start_edge_id = self._build_start_edge(
                    builder, element, edge_labels, state, target_ref
                )
                continue

            edge = CwpEdge.from_xml(element, builder.gen_edge_name())
            builder.with_edge(edge, source_ref, target_ref)

        return start_edge_id

    def _check_expressions(
        self,
        builder: CwpBuilder,
        all_items: list[Element],
        expr_lstnr: ExpressionListener,
        state: State,
        start_edge_id: str | None,
    ) -> None:
        for itm in all_items:
            style = itm.get("style")
            if style and "edgeLabel" in style:
                parent = itm.get("parent")
                expression = itm.get("value")
                if not parent:
                    raise ErrorException(CwpEdgeNoParentError(itm))
                if not expression:
                    raise ErrorException(CwpEdgeNoExpressionError(itm))
                if parent == start_edge_id:
                    continue
                builder.check_expression(expr_lstnr, expression, parent, state)

    @staticmethod
    def from_xml(root: Element, state: State) -> Result["Cwp", Error]:
        builder = CwpBuilder()
        parser = CwpXmlParser()

        try:
            mx_cells = parser._get_mx_cells(root)
            all_items = parser._get_all_items(mx_cells)
            edges = parser._get_edges(mx_cells)
            states = parser._get_states(mx_cells)
            edge_labels = parser._get_edge_labels(all_items)
            expr_lstnr = ExpressionListener(state)

            parser._add_states(builder, states)
            start_edge_id = parser._add_edges(builder, edges, edge_labels, state)
            parser._check_expressions(
                builder, all_items, expr_lstnr, state, start_edge_id
            )
        except ErrorException as e:
            assert e.args, "Error does not have enough arguments"
            return Failure(e.args[0])

        result: Result[Cwp, Error] = builder.build()
        return result


def generate_graph_viz(cwp: Cwp) -> None:
    graph_viz_visitor = CwpGraphVizVisitor()

    cwp.accept(graph_viz_visitor)

    graph_viz_visitor.dot.render("graphs/cwp_graph.gv", format="png")  # type: ignore[unused-ignore]
