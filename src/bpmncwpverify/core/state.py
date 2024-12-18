from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.tree.Tree import TerminalNode, TerminalNodeImpl
from antlr4.Token import Token

from returns.maybe import Maybe, Nothing, Some
from returns.result import Failure, Result, Success
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.functions import not_
from returns.curry import partial

from typing import Iterable, Any, cast

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.antlr.StateListener import StateListener

from bpmncwpverify.core.error import (
    Error,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
)

from bpmncwpverify.core import typechecking


def antlr_id_set_context_get_children(
    ctx: StateParser.Id_setContext,
) -> list[TerminalNodeImpl]:
    return [antlr_get_terminal_node_impl(i) for i in ctx.getChildren()]  # type: ignore[unused-ignore]


def antlr_get_id_set_context(ctx: Any) -> Maybe[StateParser.Id_setContext]:
    if ctx is None:
        return Nothing
    assert isinstance(ctx, StateParser.Id_setContext)
    return Some(ctx)


def antlr_get_terminal_node_impl(node: TerminalNode | None) -> TerminalNodeImpl:
    assert isinstance(node, TerminalNodeImpl)
    return node


def antlr_get_text(node: TerminalNodeImpl | StateParser.TypeContext) -> str:
    text: str | None = node.getText()
    assert isinstance(text, str)
    return text


def antlr_get_type_from_type_context(
    ctx: StateParser.Const_var_declContext | StateParser.Var_declContext,
) -> str:
    type_context: Any = ctx.type_()
    assert isinstance(type_context, StateParser.TypeContext)
    return antlr_get_text(type_context)


class ThrowingErrorListener(ErrorListener):  # type: ignore[misc]
    def __init__(self) -> None:
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
        msg = "line {}:{} {}".format(line, column, msg)
        raise ParseCancellationException(msg)


def _get_parser(file_contents: str) -> Result[StateParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = StateLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = StateParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)  # type: ignore[unused-ignore]
    parser.addErrorListener(ThrowingErrorListener())  # type: ignore[unused-ignore]
    return Success(parser)


def _parse_state(parser: StateParser) -> Result[StateParser.StateContext, Error]:
    try:
        tree: StateParser.StateContext = parser.state()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = StateSyntaxError(msg)
        return Failure(failure_value)


class State:
    __slots__ = ["_consts", "_enums", "_id2type", "_vars"]

    class _Listener(StateListener):  # type: ignore[misc]
        __slots__ = ["_duplicates", "_first_def", "symbol_table"]

        def __init__(self) -> None:
            super().__init__()
            self._duplicates: dict[str, tuple[int, int]] = dict()
            self._first_def: dict[str, tuple[int, int]] = dict()
            self.symbol_table: "State" = State()

        @staticmethod
        def _add_definition(
            definitions: dict[str, tuple[int, int]], id: str, line: int, column: int
        ) -> None:
            if id in definitions:
                prev_line = definitions[id][0]
                prev_column = definitions[id][1]
                error = StateMultipleDefinitionError(
                    id, line, column, prev_line, prev_column
                )
                raise Exception(error)
            else:
                definitions[id] = (line, column)

        @staticmethod
        def _get_id_and_add_definition(
            definitions: dict[str, tuple[int, int]], id_node: TerminalNodeImpl
        ) -> str:
            id: str = antlr_get_text(id_node)
            symbol: Token = id_node.getSymbol()
            State._Listener._add_definition(
                definitions, id, cast(int, symbol.line), cast(int, symbol.column)
            )
            return id

        @staticmethod
        def _get_values(
            definitions: dict[str, tuple[int, int]],
            ctx: Maybe[StateParser.Id_setContext],
        ) -> set[str]:
            if ctx == Nothing:
                return set()
            get_id = State._Listener._get_id_and_add_definition
            return {
                get_id(definitions, i)
                for i in antlr_id_set_context_get_children(ctx.unwrap())
            }

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext) -> None:
            get_id = State._Listener._get_id_and_add_definition
            node = antlr_get_terminal_node_impl(ctx.ID())
            id: str = get_id(self._first_def, node)
            values: set[str] = State._Listener._get_values(
                self._first_def,
                antlr_get_id_set_context(ctx.id_set()),
            )

            self.symbol_table._add_enum_type_decl(id, values)

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext) -> None:
            get_id = State._Listener._get_id_and_add_definition
            node = antlr_get_terminal_node_impl(ctx.ID(0))
            id: str = get_id(self._first_def, node)
            type_: str = antlr_get_type_from_type_context(ctx)
            node = antlr_get_terminal_node_impl(ctx.ID(1))
            init = antlr_get_text(node)
            self.symbol_table._add_const_decl(id, type_, init)

        def exitVar_decl(self, ctx: StateParser.Var_declContext) -> None:
            get_id = State._Listener._get_id_and_add_definition
            node = antlr_get_terminal_node_impl(ctx.ID(0))
            id: str = get_id(self._first_def, node)
            type_: str = antlr_get_type_from_type_context(ctx)
            init_node: TerminalNode = antlr_get_terminal_node_impl(ctx.ID(1))
            init: str = antlr_get_text(init_node)

            definitions: dict[str, tuple[int, int]] = dict()
            values: set[str] = State._Listener._get_values(
                definitions,
                antlr_get_id_set_context(ctx.id_set()),
            )

            if len(values) != 0 and init not in values:
                symbol: Token = init_node.getSymbol()
                error = StateInitNotInValues(
                    init, cast(int, symbol.line), cast(int, symbol.column), values
                )
                raise Exception(error)

            self.symbol_table._add_var_decl(id, type_, init, values)

    def __init__(self) -> None:
        self._consts: dict[str, tuple[str, str]] = dict()
        self._enums: dict[str, set[str]] = dict()
        self._id2type: dict[str, str] = dict()
        self._vars: dict[str, tuple[str, str, set[str]]] = dict()

    def __str__(self) -> str:
        raise NotImplementedError("SymbolTable::__str__")

    def _add_enum_type_decl(self, id: str, values: set[str]) -> None:
        # requires
        assert id not in self._id2type and id not in self._enums
        for i in values:
            assert i not in self._id2type

        self._enums[id] = values
        self._id2type[id] = typechecking.ENUM

        for v in values:
            self._id2type[v] = id

    def _add_const_decl(self, id: str, type: str, init: str) -> None:
        # requires
        assert id not in self._id2type and id not in self._consts

        self._consts[id] = (type, init)
        self._id2type[id] = type

    def _add_var_decl(self, id: str, type: str, init: str, values: set[str]) -> None:
        # requires
        assert (
            id not in self._id2type
            and id not in self._vars
            and (len(values) == 0 or init in values)
        )

        self._vars[id] = (type, init, values)
        self._id2type[id] = type

    @staticmethod
    def _build(context: StateParser.StateContext) -> Result["State", Error]:
        listener = State._Listener()
        try:
            walker: ParseTreeWalker = cast(ParseTreeWalker, ParseTreeWalker.DEFAULT)
            walker.walk(listener, context)
            return Success(listener.symbol_table)
        except Exception as exception:
            # requires
            assert len(exception.args) == 1
            error: Error = exception.args[0]
            return Failure(error)

    @staticmethod
    def _type_check_assigns(
        symbol_table: "State", ltype: str, values: Iterable[str]
    ) -> Result[tuple[()], Error]:
        get_type_init = partial(State.get_type, symbol_table)
        get_type_assign = partial(typechecking.get_type_assign, ltype)
        for i in values:
            result: Result[str, Error] = flow(
                i, get_type_init, bind_result(get_type_assign)
            )
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(())

    @staticmethod
    def _type_check_consts(symbol_table: "State") -> Result["State", Error]:
        type_check_assigns = partial(State._type_check_assigns, symbol_table)
        for key in symbol_table._consts:
            type_, init = symbol_table._consts[key]
            result = type_check_assigns(type_, [init])
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(symbol_table)

    @staticmethod
    def _type_check_vars(symbol_table: "State") -> Result["State", Error]:
        type_check_assigns = partial(State._type_check_assigns, symbol_table)
        for key in symbol_table._vars:
            type_, init, values = symbol_table._vars[key]
            result = type_check_assigns(type_, {init}.union(values))
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(symbol_table)

    @staticmethod
    def _type_check(symbol_table: "State") -> Result["State", Error]:
        result: Result["State", Error] = flow(
            symbol_table,
            State._type_check_consts,
            bind_result(State._type_check_vars),
        )

        return result

    def get_type(self, id: str) -> Result[str, Error]:
        if id in self._id2type:
            return Success(self._id2type[id])
        result: Result[str, Error] = typechecking.get_type_literal(id)
        return result

    def is_defined(self, id: str) -> bool:
        defined: bool = is_successful(self.get_type(id))
        return defined

    @staticmethod
    def build(state_def: str) -> Result["State", Error]:
        result: Result["State", Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(State._build),
            bind_result(State._type_check),
        )
        return result
