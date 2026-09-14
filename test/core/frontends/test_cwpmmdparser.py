# type: ignore
import pytest
from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Failure, Success

from bpmncwpverify.core.error import ErrorException
from bpmncwpverify.core.frontends.cwpMermaidParser import CwpMermaidParser


class TestCwpMermaidParserBuilderListenerStates:
    def test_exit_state_decl(self, mocker):
        mock_string_node = mocker.Mock()
        mock_string_node.getText.return_value = '"My State"'
        mock_id_node = mocker.Mock()
        mock_id_node.getText.return_value = "state1"

        mock_ctx = mocker.Mock()
        mock_ctx.STRING.return_value = mock_string_node
        mock_ctx.ID.return_value = mock_id_node

        mock_builder = mocker.Mock()
        mock_builder.with_state.return_value = mock_builder
        mock_from_mmd = mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpState.from_mmd",
            return_value="test_state",
        )

        listener = CwpMermaidParser._BuilderListener(mock_builder, mocker.Mock())
        listener.exitStateDecl(mock_ctx)

        mock_from_mmd.assert_called_once_with("state1", "My State")
        mock_builder.with_state.assert_called_once_with("test_state")
        assert listener.builder == mock_builder

    def test_exit_state_decl_no_string(self, mocker):
        mock_ctx = mocker.Mock()
        mock_ctx.STRING.return_value = None
        mock_ctx.ID.return_value = mocker.Mock()

        listener = CwpMermaidParser._BuilderListener(mocker.Mock(), mocker.Mock())

        with pytest.raises(AssertionError):
            listener.exitStateDecl(mock_ctx)

    def test_exit_state_decl_no_id(self, mocker):
        mock_ctx = mocker.Mock()
        mock_ctx.STRING.return_value = mocker.Mock()
        mock_ctx.ID.return_value = None

        listener = CwpMermaidParser._BuilderListener(mocker.Mock(), mocker.Mock())

        with pytest.raises(AssertionError):
            listener.exitStateDecl(mock_ctx)


class TestCwpMermaidParserBuilderListenerEdges:
    def test_exit_edge_transition_no_expression(self, mocker):
        mock_source_node = mocker.Mock()
        mock_source_node.getText.return_value = "src"
        mock_target_node = mocker.Mock()
        mock_target_node.getText.return_value = "target"

        mock_ctx = mocker.Mock()
        mock_ctx.ID.side_effect = lambda i: [mock_source_node, mock_target_node][i]
        mock_ctx.EXPR_CLAUSE.return_value = None

        mock_builder = mocker.Mock()
        mock_builder.gen_edge_name.return_value = "A"
        mock_builder.with_edge.return_value = mock_builder

        mock_edge = mocker.Mock()
        mock_from_mmd = mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.from_mmd",
            return_value=mock_edge,
        )

        listener = CwpMermaidParser._BuilderListener(mock_builder, mocker.Mock())
        listener.exitEdgeTransition(mock_ctx)

        mock_from_mmd.assert_called_once_with("target", "A")
        mock_builder.with_edge.assert_called_once_with(mock_edge, "src", "target")
        assert listener.builder == mock_builder

    def test_exit_edge_transition_no_src_or_target(self, mocker):
        mock_ctx = mocker.Mock()
        mock_ctx.ID.side_effect = lambda i: None if i == 0 else mocker.Mock()

        listener = CwpMermaidParser._BuilderListener(mocker.Mock(), mocker.Mock())

        with pytest.raises(AssertionError):
            listener.exitEdgeTransition(mock_ctx)

        mock_ctx2 = mocker.Mock()
        mock_ctx2.ID.side_effect = lambda i: mocker.Mock() if i == 0 else None

        with pytest.raises(AssertionError):
            listener.exitEdgeTransition(mock_ctx2)

    def test_exit_edge_transition_with_expression(self, mocker):
        mock_source_node = mocker.Mock()
        mock_source_node.getText.return_value = "src"
        mock_target_node = mocker.Mock()
        mock_target_node.getText.return_value = "target"

        mock_ctx = mocker.Mock()
        mock_ctx.ID.side_effect = lambda i: [mock_source_node, mock_target_node][i]

        mock_expr_clause_node = mocker.Mock()
        mock_expr_clause_node.getText.return_value = ":  x == 1  "
        mock_ctx.EXPR_CLAUSE.return_value = mock_expr_clause_node

        mock_builder = mocker.Mock()
        mock_builder.gen_edge_name.return_value = "A"
        mock_builder.with_edge.return_value = mock_builder

        mock_edge = mocker.Mock()
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.from_mmd",
            return_value=mock_edge,
        )
        mock_cleanup = mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.cleanup_expression",
            return_value="cleaned_expr",
        )
        mock_ast = mocker.Mock()
        mock_build_ast = mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.build_ast",
            return_value=mock_ast,
        )
        mock_result = mocker.Mock()
        mock_ast.type_check.return_value = mock_result
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.is_successful",
            return_value=True,
        )

        mock_state = mocker.Mock()
        listener = CwpMermaidParser._BuilderListener(mock_builder, mock_state)
        listener.exitEdgeTransition(mock_ctx)

        mock_cleanup.assert_called_once_with("x == 1")
        mock_build_ast.assert_called_once_with("cleaned_expr")
        mock_ast.type_check.assert_called_once_with(mock_state)
        assert mock_edge.expression == mock_ast
        mock_builder.with_edge.assert_called_once_with(mock_edge, "src", "target")

    def test_exit_edge_transition_with_expression_type_check_fails(self, mocker):
        mock_source_node = mocker.Mock()
        mock_source_node.getText.return_value = "src"
        mock_target_node = mocker.Mock()
        mock_target_node.getText.return_value = "target"

        mock_ctx = mocker.Mock()
        mock_ctx.ID.side_effect = lambda i: [mock_source_node, mock_target_node][i]

        mock_expr_clause_node = mocker.Mock()
        mock_expr_clause_node.getText.return_value = ": x == 1"
        mock_ctx.EXPR_CLAUSE.return_value = mock_expr_clause_node

        mock_builder = mocker.Mock()
        mock_builder.gen_edge_name.return_value = "A"

        mock_edge = mocker.Mock()
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.from_mmd",
            return_value=mock_edge,
        )
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.cleanup_expression",
            return_value="cleaned_expr",
        )
        mock_ast = mocker.Mock()
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.build_ast",
            return_value=mock_ast,
        )
        mock_result = mocker.Mock()
        mock_result.failure.return_value = "type error"
        mock_ast.type_check.return_value = mock_result
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.is_successful",
            return_value=False,
        )

        listener = CwpMermaidParser._BuilderListener(mock_builder, mocker.Mock())

        with pytest.raises(Exception) as exc_info:
            listener.exitEdgeTransition(mock_ctx)

        assert exc_info.value.args[0] == "type error"


class TestCwpMermaidParserFromMmd:
    def test_from_mmd_no_error(self, mocker):
        mock_builder_object = mocker.Mock()
        mock_builder_object.with_start_edge.return_value = mock_builder_object
        mock_builder_object.gen_edge_name.return_value = "Init_Edge_Name"
        mock_builder_object.build.return_value = "built_cwp"

        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpBuilder",
            return_value=mock_builder_object,
        )

        mock_tree = mocker.Mock()
        mocker.patch.object(CwpMermaidParser, "_parse_tree", return_value=mock_tree)

        mock_walker = mocker.Mock()
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.ParseTreeWalker",
            return_value=mock_walker,
        )

        mock_state = mocker.Mock()
        mock_state.vars = []

        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.build_ast",
            return_value=mocker.Mock(),
        )

        result = CwpMermaidParser.from_mmd("mmd_string", mock_state)

        mock_walker.walk.assert_called_once()
        mock_builder_object.build.assert_called_once()
        assert result == "built_cwp"

    def test_from_mmd_with_error(self, mocker):
        inner_error = mocker.Mock()
        error = ErrorException(inner_error)

        mocker.patch.object(
            CwpMermaidParser, "_parse_tree", side_effect=ErrorException(error)
        )

        mock_state = mocker.Mock()
        mock_state.vars = []

        result = CwpMermaidParser.from_mmd("mmd_string", mock_state)

        assert not_(is_successful)(result)
        assert result.failure() is error

    def test_from_mmd_error_during_walk(self, mocker):
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpBuilder",
            return_value=mocker.Mock(),
        )
        mocker.patch.object(CwpMermaidParser, "_parse_tree", return_value=mocker.Mock())
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.ParseTreeWalker",
            side_effect=ErrorException("WALK_FAILED"),
        )

        mock_state = mocker.Mock()
        mock_state.vars = []

        result = CwpMermaidParser.from_mmd("mmd_string", mock_state)

        assert not_(is_successful)(result)
        assert result.failure() == "WALK_FAILED"


class TestCwpMermaidParserVarAndArrayValues:
    def test_exit_start_transition_with_array_initial_value(self, mocker):
        mock_target_node = mocker.Mock()
        mock_target_node.getText.return_value = "start"

        mock_ctx = mocker.Mock()
        mock_ctx.ID.return_value = mock_target_node

        mock_expr_clause_node = mocker.Mock()
        mock_expr_clause_node.getText.return_value = ": a = {0}"
        mock_ctx.EXPR_CLAUSE.return_value = mock_expr_clause_node

        mock_builder = mocker.Mock()
        mock_builder.gen_edge_name.return_value = "A"
        mock_builder.with_start_edge.return_value = mock_builder

        mock_edge = mocker.Mock()
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.from_mmd",
            return_value=mock_edge,
        )

        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.cleanup_expression",
            return_value="a = {0}",
        )

        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.build_ast",
            return_value=mock_edge,
        )

        mock_edge.parse_initial_values.return_value = Success([("a", ["0"])])

        mock_state = mocker.Mock()
        mock_state.set_array_value.return_value = Success(None)

        object.__setattr__(
            mock_state,
            "assert_all_values_set",
            mocker.Mock(return_value=Success(None)),
        )

        listener = CwpMermaidParser._BuilderListener(
            mock_builder,
            mock_state,
        )

        listener.exitStartTransition(mock_ctx)

        mock_state.set_array_value.assert_called_once_with("a", ["0"])
        mock_state.assert_all_values_set.assert_called_once()
        mock_builder.with_start_edge.assert_called_once_with(mock_edge)

    def test_exit_start_transition_set_array_value_error(self, mocker):
        mock_target_node = mocker.Mock()
        mock_target_node.getText.return_value = "start"

        mock_ctx = mocker.Mock()
        mock_ctx.ID.return_value = mock_target_node

        mock_expr_clause_node = mocker.Mock()
        mock_expr_clause_node.getText.return_value = ": a = {bad}"
        mock_ctx.EXPR_CLAUSE.return_value = mock_expr_clause_node

        mock_builder = mocker.Mock()
        mock_builder.gen_edge_name.return_value = "A"

        mock_edge = mocker.Mock()
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.from_mmd",
            return_value=mock_edge,
        )
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.cleanup_expression",
            return_value="a = {bad}",
        )
        mocker.patch(
            "bpmncwpverify.core.frontends.cwpMermaidParser.CwpEdge.build_ast",
            return_value=mock_edge,
        )

        mock_edge.parse_initial_values.return_value = Success([("a", ["bad"])])

        mock_error = mocker.Mock()

        mock_state = mocker.Mock()
        mock_state.set_array_value.return_value = Failure(mock_error)

        listener = CwpMermaidParser._BuilderListener(
            mock_builder,
            mock_state,
        )

        with pytest.raises(ErrorException) as exc_info:
            listener.exitStartTransition(mock_ctx)

        assert exc_info.value.args[0] == mock_error

        mock_state.set_array_value.assert_called_once_with(
            "a",
            ["bad"],
        )
