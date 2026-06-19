from typing import Protocol, cast

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker

from bpmncwpverify.antlr.FeelExprLexer import FeelExprLexer
from bpmncwpverify.antlr.FeelExprListener import FeelExprListener
from bpmncwpverify.antlr.FeelExprParser import FeelExprParser  # type: ignore
from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BoolLiteralNode,
    DivideNode,
    EqualNode,
    ExpressionNode,
    GENode,
    GTNode,
    IfNode,
    LENode,
    LiteralNode,
    LTNode,
    MultiplyNode,
    NotEqualNode,
    NotNode,
    OrNode,
    PowerNode,
    SubNode,
)


class HasText(Protocol):
    def getText(self) -> str | None: ...


class Feel:
    __slots__ = ["ast"]

    def __init__(self, ast: ExpressionNode) -> None:
        self.ast = ast

    @classmethod
    def parse(cls, text: str) -> "Feel":
        lexer = FeelExprLexer(InputStream(text))
        stream = CommonTokenStream(lexer)
        parser = FeelExprParser(stream)

        tree = parser.compilation_unit()

        listener = cls._Listener()
        ParseTreeWalker().walk(listener, tree)

        return cls(cast(ExpressionNode, listener.ast))

    class _Listener(FeelExprListener):
        def __init__(self) -> None:
            super().__init__()
            self.stack: list[ExpressionNode] = []
            self.ast: ExpressionNode | None = None

        def exitCompilation_unit(
            self, ctx: FeelExprParser.Compilation_unitContext
        ) -> None:
            assert len(self.stack) == 1
            self.ast = self.stack.pop()

        def exitNumberLiteral(self, ctx: FeelExprParser.NumberLiteralContext) -> None:
            self.stack.append(LiteralNode(ctx.getText()))

        def exitBoolLiteral(self, ctx: FeelExprParser.BoolLiteralContext) -> None:
            if ctx.getText() == "true":
                self.stack.append(BoolLiteralNode(True))
            else:
                self.stack.append(BoolLiteralNode(False))

        def exitAddExpression(self, ctx: FeelExprParser.AddExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            if ctx.ADD():
                self.stack.append(AddNode(left, right))
            else:
                self.stack.append(SubNode(left, right))

        def exitMultExpression(self, ctx: FeelExprParser.MultExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            if ctx.MUL():
                self.stack.append(MultiplyNode(left, right))
            else:
                self.stack.append(DivideNode(left, right))

        def exitPowExpression(self, ctx: FeelExprParser.PowExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            self.stack.append(PowerNode(left, right))

        def exitCompExpression(self, ctx: FeelExprParser.CompExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            if ctx.LT():
                self.stack.append(LTNode(left, right))
            elif ctx.GT():
                self.stack.append(GTNode(left, right))
            elif ctx.LE():
                self.stack.append(LENode(left, right))
            elif ctx.GE():
                self.stack.append(GENode(left, right))
            elif ctx.EQUAL():
                self.stack.append(EqualNode(left, right))
            elif ctx.NOTEQUAL():
                self.stack.append(NotEqualNode(left, right))

        def exitCondAnd(self, ctx: FeelExprParser.CondAndContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            self.stack.append(AndNode(left, right))

        def exitCondOr(self, ctx: FeelExprParser.CondOrContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            self.stack.append(OrNode(left, right))

        def exitPrimaryIfExpression(
            self, ctx: FeelExprParser.PrimaryIfExpressionContext
        ) -> None:
            elsedo = self.stack.pop()
            thendo = self.stack.pop()
            condition = self.stack.pop()

            self.stack.append(IfNode(condition, thendo, elsedo))

        def exitFnInvocation(self, ctx: FeelExprParser.FnInvocationContext) -> None:
            fn_name = cast(
                FeelExprParser.UnaryExpressionContext, ctx.unaryExpression()
            ).getText()

            if fn_name == "not":
                self.stack.append(NotNode(self.stack.pop()))
            else:
                pass
