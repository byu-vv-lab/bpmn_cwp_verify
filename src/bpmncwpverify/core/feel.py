from typing import Protocol, cast

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from returns.result import Failure, Result, Success

from bpmncwpverify.antlr.FeelExprLexer import FeelExprLexer
from bpmncwpverify.antlr.FeelExprListener import FeelExprListener
from bpmncwpverify.antlr.FeelExprParser import FeelExprParser
from bpmncwpverify.core.error import Error, ErrorException
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
    IntervalNode,
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
    TripleListNode,
    TripleNode,
    XOrNode,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.feel_typechecker_visitor import TypeCheckerVisitor


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

        tree = parser.compilation_unit()  # type: ignore

        listener = cls._Listener()
        ParseTreeWalker().walk(listener, tree)

        return cls(cast(ExpressionNode, listener.ast))

    def type_check(self, state: State) -> Result[str, Error]:
        typechecker = TypeCheckerVisitor(state)

        try:
            self.ast.accept(typechecker)
        except ErrorException as e:
            return Failure(e.error)

        return Success(typechecker.stack.pop())

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

            if ctx.ADD():  # type: ignore
                self.stack.append(AddNode(left, right))
            else:
                self.stack.append(SubtractNode(left, right))

        def exitMultExpression(self, ctx: FeelExprParser.MultExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            if ctx.MUL():  # type: ignore
                self.stack.append(MultiplyNode(left, right))
            else:
                self.stack.append(DivideNode(left, right))

        def exitPowExpression(self, ctx: FeelExprParser.PowExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            self.stack.append(PowerNode(left, right))

        def exitSignedUnaryExpressionMinus(
            self, ctx: FeelExprParser.SignedUnaryExpressionMinusContext
        ) -> None:
            operand = self.stack.pop()
            if isinstance(operand, NumberLiteralNode):
                value = operand.value
                self.stack.append(
                    NumberLiteralNode(
                        value[1:] if value.startswith("-") else "-" + value
                    )
                )
            else:
                self.stack.append(SubtractNode(NumberLiteralNode("0"), operand))

        def exitCompExpression(self, ctx: FeelExprParser.CompExpressionContext) -> None:
            right = self.stack.pop()
            left = self.stack.pop()

            if ctx.LT():  # type: ignore
                self.stack.append(LTNode(left, right))
            elif ctx.GT():  # type: ignore
                self.stack.append(GTNode(left, right))
            elif ctx.LE():  # type: ignore
                self.stack.append(LENode(left, right))
            elif ctx.GE():  # type: ignore
                self.stack.append(GENode(left, right))
            elif ctx.EQUAL():  # type: ignore
                self.stack.append(EqualNode(left, right))
            elif ctx.NOTEQUAL():  # type: ignore
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

            if isinstance(function, QualifiedNameNode) and function.name == "not":
                self.stack.append(NotNode(argument))
            else:
                self.stack.append(function)
                self.stack.append(argument)

        def exitPrimaryList(self, ctx: FeelExprParser.PrimaryListContext) -> None:
            pass

        def exitList(self, ctx: FeelExprParser.ListContext) -> None:
            if ctx.expressionList() is None:  # type: ignore
                self.stack.append(ListNode([]))

        def exitExpressionList(self, ctx: FeelExprParser.ExpressionListContext) -> None:
            expressions = ctx.getTypedRuleContexts(FeelExprParser.ExpressionContext)

            values: list[ExpressionNode] = []

            for _ in expressions:
                values.append(self.stack.pop())

            values.reverse()

            self.stack.append(ListNode(values))

        def exitInterval(self, ctx: FeelExprParser.IntervalContext) -> None:
            upper = self.stack.pop()
            lower = self.stack.pop()

            opening = cast(HasText, ctx.getChild(0)).getText()
            closing = cast(HasText, ctx.getChild(ctx.getChildCount() - 1)).getText()

            self.stack.append(
                IntervalNode(lower, upper, opening == "[", closing == "]")
            )

        def exitChooseExpression(
            self, ctx: FeelExprParser.ChooseExpressionContext
        ) -> None:
            contents = self.stack.pop()

            assert isinstance(contents, ListNode | IntervalNode)

            self.stack.append(ChooseNode(contents))

        def exitTripExpression(self, ctx: FeelExprParser.TripExpressionContext) -> None:
            value = self.stack.pop()
            inputs = cast(ListNode, self.stack.pop())
            target = self.stack.pop()

            self.stack.append(TripleNode(target, inputs, value))

        def exitTripleList(self, ctx: FeelExprParser.TripleListContext) -> None:
            triples = ctx.getTypedRuleContexts(FeelExprParser.TripleExpressionContext)

            values: list[TripleNode] = []

            for _ in triples:
                values.append(cast(TripleNode, self.stack.pop()))

            values.reverse()

            self.stack.append(TripleListNode(values))
