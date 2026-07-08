from typing import Protocol, cast

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker

from bpmncwpverify.antlr.FeelExprLexer import FeelExprLexer
from bpmncwpverify.antlr.FeelExprListener import FeelExprListener
from bpmncwpverify.antlr.FeelExprParser import FeelExprParser  # type: ignore
from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BoolLiteralNode,
    ChooseNode,
    DivideNode,
    EqualNode,
    ExpressionNode,
    GENode,
    GTNode,
    IfNode,
    LENode,
    ListNode,
    LTNode,
    MultiplyNode,
    NotEqualNode,
    NotNode,
    NumberLiteralNode,
    OrNode,
    PowerNode,
    QualifiedNameNode,
    SubtractNode,
    TripleNode,
    XOrNode,
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
            self.stack.append(NumberLiteralNode(ctx.getText()))

        def exitBoolLiteral(self, ctx: FeelExprParser.BoolLiteralContext) -> None:
            self.stack.append(BoolLiteralNode(ctx.getText()))

        def exitQualifiedName(self, ctx: FeelExprParser.QualifiedNameContext) -> None:
            self.stack.append(QualifiedNameNode(ctx.getText()))

        def exitAddExpression(self, ctx: FeelExprParser.AddExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            if ctx.ADD():
                self.stack.append(AddNode(left, right))
            else:
                self.stack.append(SubtractNode(left, right))

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

        def exitCondXOr(self, ctx: FeelExprParser.CondXOrContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            self.stack.append(XOrNode(left, right))

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
            argument = self.stack.pop()
            function = self.stack.pop()

            assert isinstance(function, QualifiedNameNode)

            if function.name == "not":
                self.stack.append(NotNode(argument))
            else:
                pass

        def exitPrimaryList(self, ctx: FeelExprParser.PrimaryListContext) -> None:
            pass

        def exitList(self, ctx: FeelExprParser.ListContext) -> None:
            if ctx.expressionList() is None:
                self.stack.append(ListNode([]))

        def exitExpressionList(self, ctx: FeelExprParser.ExpressionListContext) -> None:
            expressions = ctx.getTypedRuleContexts(FeelExprParser.ExpressionContext)

            values: list[ExpressionNode] = []

            for _ in expressions:
                values.append(self.stack.pop())

            values.reverse()

            self.stack.append(ListNode(values))

        def exitChooseExpression(
            self, ctx: FeelExprParser.ChooseExpressionContext
        ) -> None:
            contents = cast(ListNode, self.stack.pop())

            self.stack.append(ChooseNode(contents))

        def exitTripExpression(self, ctx: FeelExprParser.TripExpressionContext) -> None:
            value = self.stack.pop()
            inputs = cast(ListNode, self.stack.pop())
            target = self.stack.pop()

            self.stack.append(TripleNode(target, inputs, value))
