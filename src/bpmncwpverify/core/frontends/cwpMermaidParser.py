from typing import Any, cast

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Failure, Result

from bpmncwpverify.antlr.CwpLexer import CwpLexer
from bpmncwpverify.antlr.CwpParser import CwpParser
from bpmncwpverify.antlr.CwpParserListener import CwpParserListener
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.error import Error
from bpmncwpverify.core.state import State


class CwpMermaidParser:
    class _BuilderListener(CwpParserListener):
        def __init__(self, builder: "CwpBuilder", state: State):
            self.builder = builder
            self.state = state

        def exitStateDecl(self, ctx: CwpParser.StateDeclContext) -> None:
            string_node = cast(Any, ctx).STRING()
            id_node = cast(Any, ctx).ID()

            assert string_node is not None, "STRING is required by grammar"
            assert id_node is not None, "ID is required by grammar"

            display_name: str = string_node.getText().strip('"')
            state_id: str = id_node.getText()

            state = CwpState.from_mmd(state_id, display_name)
            self.builder = self.builder.with_state(state)

        def exitEdgeTransition(self, ctx: CwpParser.EdgeTransitionContext) -> None:
            source_node = cast(Any, ctx).ID(0)
            target_node = cast(Any, ctx).ID(1)

            assert source_node is not None and target_node is not None

            source_id: str = source_node.getText()
            target_id: str = target_node.getText()

            edge = CwpEdge.from_mmd(
                target_id,
                self.builder.gen_edge_name(),
            )

            expr_ctx = cast(Any, ctx).expr()
            if expr_ctx is not None:
                raw_expr: str = expr_ctx.getText().strip()
                edge.expression = CwpEdge.cleanup_expression(raw_expr)
                edge.expression = CwpEdge.build_ast(edge.expression)

                result = edge.expression.type_check(self.state)
                if not_(is_successful)(result):
                    raise Exception(result.failure())

            self.builder = self.builder.with_edge(
                edge,
                source_id,
                target_id,
            )

    @staticmethod
    def _parse_tree(mmd_str: str) -> CwpParser.DiagramContext:
        lexer = CwpLexer(InputStream(mmd_str))
        token_stream = CommonTokenStream(lexer)
        parser = CwpParser(token_stream)

        return cast(CwpParser.DiagramContext, cast(Any, parser).diagram())

    @staticmethod
    def from_mmd(mmd_str: str, state: State) -> Result["Cwp", Error]:
        listener = CwpMermaidParser._BuilderListener(CwpBuilder(), state)

        try:
            tree = CwpMermaidParser._parse_tree(mmd_str)
            ParseTreeWalker().walk(listener, tree)

            clauses = [f"{v.id} == {v.init.value}" for v in state.vars]
            start_edge = CwpEdge("Init_Edge", listener.builder.gen_edge_name())
            start_edge.expression = " && ".join(clauses)
            listener.builder = listener.builder.with_start_edge(start_edge)
        except Exception as e:
            assert e.args, "Error does not have enough arguments"
            return Failure(e.args[0])

        result: Result[Cwp, Error] = listener.builder.build()
        return result
