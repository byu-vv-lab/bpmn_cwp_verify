# type: ignore
from antlr4 import CommonTokenStream, InputStream

from bpmncwpverify.antlr.FeelExprLexer import FeelExprLexer
from bpmncwpverify.antlr.FeelExprParser import FeelExprParser
from bpmncwpverify.core.feel_tree import AddNode, LiteralNode
from bpmncwpverify.visitors.feel_visitor import FeelExprBuilder


def test_ast_builder_runs():
    text = "1 + 2"

    lexer = FeelExprLexer(InputStream(text))
    tokens = CommonTokenStream(lexer)

    parser = FeelExprParser(tokens)

    parse_tree = parser.compilation_unit()

    ast = FeelExprBuilder().visit(parse_tree)

    assert ast is not None


def test_addition_ast():
    text = "1 + 2"

    lexer = FeelExprLexer(InputStream(text))
    tokens = CommonTokenStream(lexer)

    parser = FeelExprParser(tokens)

    parse_tree = parser.compilation_unit()

    builder = FeelExprBuilder()

    ast = builder.visit(parse_tree)

    assert isinstance(ast, AddNode)

    assert isinstance(ast.left, LiteralNode)
    assert isinstance(ast.right, LiteralNode)

    assert ast.left.value == 1
    assert ast.right.value == 2
