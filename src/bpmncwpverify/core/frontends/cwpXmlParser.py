from xml.etree.ElementTree import Element

from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Failure, Result

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
        if (mx_graph_model := diagram.find("mxGraphModel")) is None:
            raise ErrorException(CwpFileStructureError("mxGraphModel"))
        if (mx_root := mx_graph_model.find("root")) is None:
            raise ErrorException(CwpFileStructureError("root"))
        if not (mx_cells := mx_root.findall("mxCell")):
            raise ErrorException(CwpFileStructureError("mxCell"))
        if object := mx_root.findall("object"):
            raise ErrorException(CwpUnsupportedElementError(len(object), "object"))
        return mx_cells

    def _get_all_items(self, mx_cells: list[Element]) -> list[Element]:
        return [itm for itm in mx_cells]

    def _get_edges(self, mx_cells: list[Element]) -> list[Element]:
        return [itm for itm in mx_cells if itm.get("edge")]

    def _get_states(self, mx_cells: list[Element]) -> list[Element]:
        return [itm for itm in mx_cells if itm.get("vertex")]

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

    def _add_edges(self, builder: CwpBuilder, edges: list[Element]) -> None:
        for element in edges:
            source_ref = element.get("source")
            target_ref = element.get("target")
            if not target_ref or not source_ref:
                raise ErrorException(CwpEdgeNoStateError(element))
            edge = CwpEdge.from_xml(element, builder.gen_edge_name())

            builder = builder.with_edge(edge, source_ref, target_ref)

    def _add_incoming_edge_to_start_state(
        self, builder: CwpBuilder, state: State
    ) -> None:
        expr: list[str] = []
        for v in state.vars:
            expr.append(f"{v.id} = {v.init.value}")

        edge_expr = " and ".join(expr)

        edge = CwpEdge("Init_Edge", builder.gen_edge_name())
        edge.expression = CwpEdge.build_ast(edge_expr)
        result = edge.expression.type_check(state)

        if not_(is_successful)(result):
            raise ErrorException(result.failure())

        builder = builder.with_start_edge(edge)

    def _check_expressions(
        self,
        builder: CwpBuilder,
        all_items: list[Element],
        expr_lstnr: ExpressionListener,
        state: State,
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
            expr_lstnr = ExpressionListener(state)
            parser._add_states(builder, states)
            parser._add_edges(builder, edges)
            parser._add_incoming_edge_to_start_state(builder, state)
            parser._check_expressions(builder, all_items, expr_lstnr, state)
        except ErrorException as e:
            return Failure(e.error)

        result: Result[Cwp, Error] = builder.build()
        return result


def generate_graph_viz(cwp: Cwp) -> None:
    graph_viz_visitor = CwpGraphVizVisitor()

    cwp.accept(graph_viz_visitor)

    graph_viz_visitor.dot.render("graphs/cwp_graph.gv", format="png")  # type: ignore[unused-ignore]
