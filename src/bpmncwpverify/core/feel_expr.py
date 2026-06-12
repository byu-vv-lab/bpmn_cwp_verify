from typing import Any

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.error.ErrorStrategy import ParseCancellationException
from returns.curry import partial
from returns.functions import not_
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.result import Failure, Result, Success

from bpmncwpverify.antlr.FeelExprLexer import FeelExprLexer
from bpmncwpverify.antlr.FeelExprListener import FeelExprListener
from bpmncwpverify.antlr.FeelExprParser import (  # type: ignore[attr-defined]
    FeelExprParser,
)
from bpmncwpverify.core import feel_typechecking
from bpmncwpverify.core.error import (
    Error,
    ExpressionComputationCompatabilityError,
    ExpressionParseError,
    ExpressionRelationCompatabilityError,
    ExpressionUnrecognizedID,
)
from bpmncwpverify.core.state import (
    State,
    antlr_get_terminal_node_impl,
    antlr_get_text,
)


class ThrowingErrorListener(ErrorListener):  # type: ignore[misc]
    """
    Used to replace default error listener
    """

    def __init__(self) -> None:
        """
        Initialize ThrowingErrorListener object
        """
        super().__init__()

    def syntaxError(
        self,
        recognizer: Any,
        offendingSymbol: Any,
        line: int,
        column: int,
        msg: str,
        e: Exception,
    ) -> None:
        """
        Raises ParseCancellationException when a syntax error is encountered

        Args:
            recognizer (Any): Either the parser or lexer that encountered the error
            offendingSymbol (Any): Token/symbol that caused syntax error
            line (int): Line where error occured
            column (int): Position in line where error occured
            msg (str): Error message passed along by the recognizer
            e (Exception): Exception associated with error
        """
        msg = f"line {line}:{column} {msg}"
        raise ParseCancellationException(msg)


def _get_parser(file_contents: str) -> Result[FeelExprParser, Error]:
    """
    Returns an ExprParser object if the contents of the file are valid, error otherwise

    Args:
        file_contents (str): Contents of the file
    """
    # Create InputStream object with contents of the file
    input_stream = InputStream(file_contents)
    # Create ExprLexer object with previously created InputStream object to tokenize file contents
    lexer = FeelExprLexer(input_stream)
    # Create a CommonTokenStream object with the tokens in ExprLexer object
    stream = CommonTokenStream(lexer)
    # Create ExprParser object with previously created CommonTokenStream object
    parser = FeelExprParser(stream)
    # Remove default error listener from ExprParser object
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)  # type: ignore[unused-ignore]
    # Add new error listener with ThrowingErrorListener object
    parser.addErrorListener(ThrowingErrorListener())  # type: ignore[unused-ignore]
    return Success(parser)


def _parse_expressions(
    parser: FeelExprParser,
) -> Result[FeelExprParser.Compilation_unitContext, Error]:
    """
    Returns a traversable tree object if successful, error otherwise

    Args:
        parser (ExprParser): Parser that will make sure tree is valid
    """
    try:
        tree: FeelExprParser.Compilation_unitContext = parser.compilation_unit()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = ExpressionParseError(msg)
        return Failure(failure_value)


class ExpressionListener(FeelExprListener):
    """
    Verifies expressions
    Contains interface used to interact with other classes outside of expression checking functionality
    """

    __slots__ = ["state", "type_stack", "final_type"]

    def __init__(self, state: State) -> None:
        """
        Initialize ExpressionListener object

        Args:
            state (State): State object that identifies variable typing
        """
        self.final_type: str
        self.state = state
        self.type_stack: list[str] = []

    def check_arithmetic_types(self, left_type: str, right_type: str) -> None:
        """
        Check if expressions using +, -, * or / are valid expressions then appends resulting type to type stack,
        raise ExpressionComputationCompatabilityError otherwise

        Args:
            left_type (str): Variable type left of the operator
            right_type (str): Variable type right of the operator
        """
        if not_(is_successful)(
            result := feel_typechecking.get_computation_type_result(
                left_type, right_type, ExpressionComputationCompatabilityError
            )
        ):
            raise Exception(result.failure())
        self.type_stack.append(result.unwrap())

    def check_and_or_types(self, left_type: str, right_type: str) -> None:
        """
        Check if expressions using && or || are valid expressions then appends resulting type to type stack,
        raise ExpressionRelationCompatabilityError otherwise

        Args:
            left_type (str): Variable type left of the operator
            right_type (str): Variable type right of the operator
        """
        if not_(is_successful)(
            result := feel_typechecking.get_and_or_type_result(
                left_type, right_type, ExpressionRelationCompatabilityError
            )
        ):
            raise Exception(result.failure())
        self.type_stack.append(result.unwrap())

    def exitStart(self, ctx: FeelExprParser.Compilation_unitContext) -> None:
        """
        Sets the final type of the expression to the final type stored in the type stack

        Args:
            ctx (ExprParser.StartContext): Type of node that parser is traversing through
        """
        self.final_type = self.type_stack.pop()

    def exitOr(self, ctx: FeelExprParser.ConditionalOrExpressionContext) -> None:
        """
        Verify that left and right types of an expression using || are valid

        Args:
            ctx (ExprParser.OrContext): Type of node that parser is traversing through
        """
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_and_or_types(left_type, right_type)

    def exitAnd(self, ctx: FeelExprParser.ConditionalAndExpressionContext) -> None:
        """
        Verify that left and right types of an expression using && are valid

        Args:
            ctx (ExprParser.AndContext): Type of node that parser is traversing through
        """
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_and_or_types(left_type, right_type)

    def exitRelational(self, ctx: FeelExprParser.RelationalExpressionContext) -> None:
        """
        Verify that left and right types of an expression using <, <=, ==, !=, >, or >= are valid,
        raise ExpressionRelationCompatabilityError otherwise

        Args:
            ctx (ExprParser.RelationalContext): Type of node that parser is traversing through
        """
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        if not_(is_successful)(
            result := feel_typechecking.get_relational_type_result(
                left_type, right_type, ExpressionRelationCompatabilityError
            )
        ):
            raise Exception(result.failure())
        self.type_stack.append(feel_typechecking.BOOL)

    def exitAddSub(self, ctx: FeelExprParser.AdditiveExpressionContext) -> None:
        """
        Verify that left and right types of an expression using + or - are valid

        Args:
            ctx (ExprParser.AddSubContext): Type of node that parser is traversing through
        """
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_arithmetic_types(left_type, right_type)

    def exitMulDiv(self, ctx: FeelExprParser.MultiplicativeExpressionContext) -> None:
        """
        Verify that left and right types of an expression using * or / are valid

        Args:
            ctx (ExprParser.MulDivContext): Type of node that parser is traversing through
        """
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_arithmetic_types(left_type, right_type)

    def enterID(self, ctx: FeelExprParser.NameRefContext) -> None:
        """
        Retrieve variable type of given ID, raise ExpressionUnrecognizedID otherwise

        Args:
            ctx (ExprParser.IDContext): Type of node that parser is traversing through
        """
        node = antlr_get_terminal_node_impl(ctx.Identifier())
        identifier = antlr_get_text(node)
        type = self.state.get_type(identifier)  # Variable type retrieval method
        if not_(is_successful)(type):
            raise Exception(ExpressionUnrecognizedID(identifier))
        self.type_stack.append(type.unwrap())

    @staticmethod
    def _build(
        state: State, context: FeelExprParser.ExpressionContext
    ) -> Result[str, Error]:
        """
        Static method used to build the tree walker and return the final type of the given expression, error otherwise

        Args:
            state (State): State object that holds variable typing
            context (ExprParser.ExprContext): Provides the grammar context to be used for the tree walker
        """
        listener = ExpressionListener(state)
        try:
            walker: ParseTreeWalker = ParseTreeWalker.DEFAULT
            walker.walk(listener, context)
            result: Result[str, Error] = Success(listener.final_type)
            return result
        except Exception as exception:
            assert len(exception.args) == 1
            error: Error = exception.args[0]
            return Failure(error)

    @staticmethod
    def type_check(expression: str, state: State) -> Result[str, Error]:
        """
        Interface used to interact with code outside of expression type checking functionality
        Returns final type of expression, error otherwise

        Args:
            expression (str): Expression to be evaluated
            state (State): State object that holds variable typing
        """
        build_with_params = partial(ExpressionListener._build, state)
        # flow will allow result of previous code in previous line to pipeline into next function/line of code
        result: Result[str, Error] = flow(
            expression,
            _get_parser,
            bind_result(_parse_expressions),
            bind_result(build_with_params),
        )
        return result
