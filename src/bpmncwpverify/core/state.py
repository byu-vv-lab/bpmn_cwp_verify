import builtins

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.Token import Token
from antlr4.tree.Tree import TerminalNode, TerminalNodeImpl

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateListener import StateListener
from bpmncwpverify.antlr.StateParser import StateParser

from bpmncwpverify.core import typechecking

from bpmncwpverify.core.error import (
    Error,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
)

from returns.curry import partial
from returns.functions import not_
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.result import Failure, Result, Success

from typing import Any, cast, Iterable


def antlr_id_set_context_get_children(
    ctx: StateParser.Id_setContext,
) -> list[TerminalNodeImpl]:
    """
    Returns a list of nodes of type ID from a node of type ID set

    Args:
        ctx (StateParser.Id_setContext): Node where list of IDs can be traversed
    """
    return [antlr_get_terminal_node_impl(i) for i in ctx.getChildren()]  # type: ignore[unused-ignore]


def antlr_get_id_set_context(ctx: Any) -> Maybe[StateParser.Id_setContext]:
    """
    Verifies if node is of type ID set

    Args:
        ctx (Any): The node to check if it is of type ID set

    Returns:
        StateParser.Id_setContext: Node if node is of type ID set
        None: If node is of type None
        AssertionError: If node is not None and not of type ID set
    """
    if ctx is None:
        return Nothing
    assert isinstance(ctx, StateParser.Id_setContext)
    return Some(ctx)


def antlr_get_terminal_node_impl(node: TerminalNode | None) -> TerminalNodeImpl:
    """
    Verifies and returns the node if node is a terminal node/leaf node, AssertionError otherwise

    Args:
        ctx (TerminalNode | None): The node to check if it is a leaf node
    """
    assert isinstance(node, TerminalNodeImpl)
    return node


def antlr_get_text(node: TerminalNodeImpl | StateParser.TypeContext) -> str:
    """
    Returns the text within the node

    Args:
        ctx (TerminalNodeImpl | StateParser.TypeContext): The node to retrieve the text
    """
    text: str | None = node.getText()
    assert isinstance(text, str)
    return text


def antlr_get_type_from_type_context(
    ctx: StateParser.Const_var_declContext | StateParser.Var_declContext,
) -> str:
    """
    Returns the type contained in a Type node

    Args:
        ctx (StateParser.Const_var_declContext | StateParser.Var_declContext): The node to retrieve the type
    """
    type_context: Any = ctx.type_()
    assert isinstance(type_context, StateParser.TypeContext)
    return antlr_get_text(type_context)


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
        msg = "line {}:{} {}".format(line, column, msg)
        raise ParseCancellationException(msg)


def _get_parser(file_contents: str) -> Result[StateParser, Error]:
    """
    Returns an StateParser object if the contents of the file are valid, error otherwise

    Args:
        file_contents (str): Contents of the file
    """
    # Create InputStream object with contents of the file
    input_stream = InputStream(file_contents)
    # Create StateLexer object with previously created InputStream object to tokenize file contents
    lexer = StateLexer(input_stream)
    # Create a CommonTokenStream object with the tokens in StateLexer object
    stream = CommonTokenStream(lexer)
    # Create StateParser object with previously created CommonTokenStream object
    parser = StateParser(stream)
    # Remove default error listener from StateParser object
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)  # type: ignore[unused-ignore]
    # Add new error listener with ThrowingErrorListener object
    parser.addErrorListener(ThrowingErrorListener())  # type: ignore[unused-ignore]
    return Success(parser)


def _parse_state(parser: StateParser) -> Result[StateParser.StateContext, Error]:
    """
    Returns a traversable tree object if successful, error otherwise

    Args:
        parser (StateParser): Parser that will make sure tree is valid
    """
    try:
        tree: StateParser.StateContext = parser.state()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = StateSyntaxError(msg)
        return Failure(failure_value)


class DeclLoc:
    """
    Parent class for all types of variable declarations, stores location of variable declaration
    """

    __slots__ = ["line", "col"]

    def __init__(self, line: Maybe[int], col: Maybe[int]) -> None:
        """
        Initialize DeclLoc object

        Args:
            line (Maybe[int]): Possible line number of variable declaration
            col (Maybe[int]): Possible character position in the line of variable declaration
        """
        self.line = line
        self.col = col


class AllowedValueDecl(DeclLoc):
    """
    Values allowed to be associated with said variable declaration
    """

    __slots__ = ["value"]

    def __init__(
        self, value: str, line: Maybe[int] = Nothing, col: Maybe[int] = Nothing
    ) -> None:
        """
        Initialize AllowedValueDecl object

        Args:
            value (str): Value associated with the variable declaration
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        super().__init__(line, col)
        self.value = value


class ConstDecl(DeclLoc):
    """
    Represents constant varaible declaration using keyword const
    """

    __slots__ = ["id", "type_", "init"]

    def __init__(
        self,
        id: str,
        type_: str,
        init: AllowedValueDecl,
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        """
        Initialize ConstDecl object

        Args:
            id (str): Variable name
            type_ (str): Variable type
            init (AllowedValueDecl): Variable value
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        super().__init__(line, col)
        self.id = id
        self.type_ = type_
        self.init = init


class EnumDecl(DeclLoc):
    """
    Represents enumeration varaible declaration using keyword enum
    """

    __slots__ = ["id", "values"]

    def __init__(
        self,
        id: str,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        """
        Initialize EnumDecl object

        Args:
            id (str): Variable name
            values (list[AllowedValueDecl]): Variable values
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        super().__init__(line, col)
        self.id = id
        self.values = values


class VarDecl(DeclLoc):
    """
    Represents variable declaration using keyword var
    """

    __slots__ = ["id", "type_", "init", "values", "line", "col"]

    def __init__(
        self,
        id: str,
        type_: str,
        init: AllowedValueDecl,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        """
        Initialize VarDecl object

        Args:
            id (str): Variable name
            type_ (str): Variable type
            init (AllowedValueDecl): Initial variable value
            values (list[AllowedValueDecl]): Variable values
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        super().__init__(line, col)
        self.id = id
        self.type_ = type_
        self.init = init
        self.values = values

    @staticmethod
    def var_decl(
        id: str,
        type_: str,
        init: AllowedValueDecl,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> Result["VarDecl", Error]:
        """
        Returns a VarDecl object if the length of list of values is 0 or if init is contained in the list of values, error otherwise

        Args:
            id (str): Variable name
            type_ (str): Variable type
            init (AllowedValueDecl): Initial variable value
            values (list[AllowedValueDecl]): Variable values
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        value_ids = {i.value for i in values}
        if len(values) == 0 or init.value in value_ids:
            return Success(VarDecl(id, type_, init, values, line, col))
        else:
            return Failure(
                StateInitNotInValues(init.value, init.line, init.col, value_ids)
            )


class TypeWithDeclLoc:
    """
    Stores type related to variable in stored location
    """

    __slots__ = ["type_", "decl_loc"]

    def __init__(self, type_: str, decl_loc: DeclLoc) -> None:
        """
        Initialize TypeWithDeclLoc object

        Args:
            type_ (str): Type of the variable
            decl_loc (DeclLoc): Location of variable
        """
        self.type_ = type_
        self.decl_loc = decl_loc


class StateBuilder:
    """
    Store variable information
    """

    __slots__ = ["_consts", "_enums", "_vars"]

    def __init__(self) -> None:
        """
        Initialize StateBuilder object
        """
        self._consts: list[ConstDecl] = list()
        self._enums: list[EnumDecl] = list()
        self._vars: list[VarDecl] = list()

    def with_enum_type_decl(self, enum_decl: EnumDecl) -> "StateBuilder":
        """
        Add to list of enum variables

        Args:
            enum_decl (EnumDecl): variable to add to list
        """
        self._enums.append(enum_decl)
        return self

    def with_const_decl(self, const_decl: ConstDecl) -> "StateBuilder":
        """
        Add to list of const variables

        Args:
            const_decl (ConstDecl): variable to add to list
        """
        self._consts.append(const_decl)
        return self

    def with_var_decl(self, var_decl: VarDecl) -> "StateBuilder":
        """
        Add to list of var variables

        Args:
            var_decl (VarDecl): variable to add to list
        """
        self._vars.append(var_decl)
        return self

    def build(self) -> Result["State", Error]:
        """
        Create a State object with the given lists of variables stored within itself
        """
        state = State(self._consts, self._enums, self._vars)
        return State.type_check(state)


class State:
    """
    Verifies variable declaration integrity
    Contains interface method used to interact with code outside of variable declaration checking functionality
    """

    __slots__ = ["_consts", "_enums", "_id2type", "_vars"]

    class _Listener(StateListener):  # type: ignore[misc]
        """
        Adds variables to lists stored in StateBuilder object
        """

        __slots__ = ["state_builder", "error"]

        def __init__(self) -> None:
            """
            Initialize _Listener object
            """
            super().__init__()
            self.state_builder: "StateBuilder" = StateBuilder()
            self.error: Maybe[Error] = Nothing

        @staticmethod
        def _get_id(id_node: TerminalNodeImpl) -> str:
            """
            Return ID of given node

            Args:
                id_node (TerminalNodeImpl): Node to get ID from
            """
            id: str = antlr_get_text(id_node)
            return id

        @staticmethod
        def _get_value_decl(id_node: TerminalNodeImpl) -> AllowedValueDecl:
            """
            Return the value of the variable declaration

            Args:
                id_node (TerminalNodeImpl): Node to get value from
            """
            id: str = antlr_get_text(id_node)
            symbol: Token = id_node.getSymbol()
            return AllowedValueDecl(
                id, Some(cast(int, symbol.line)), Some(cast(int, symbol.column))
            )

        @staticmethod
        def _get_values(
            ctx: Maybe[StateParser.Id_setContext],
        ) -> list[AllowedValueDecl]:
            """
            Return values from a list of nodes

            Args:
                ctx (Maybe[StateParser.Id_setContext]): Node that contains a list of children to get values from
            """
            if ctx == Nothing:
                return list()
            return [
                State._Listener._get_value_decl(i)
                for i in antlr_id_set_context_get_children(ctx.unwrap())
            ]

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext) -> None:
            """
            Add new enum variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Enum_type_declContext): Enum variable to add
            """
            node = antlr_get_terminal_node_impl(ctx.ID())
            symbol: Token = node.getSymbol()
            id: str = State._Listener._get_id(node)
            id_line = Some(cast(int, symbol.line))
            id_col = Some(cast(int, symbol.column))

            values: list[AllowedValueDecl] = State._Listener._get_values(
                antlr_get_id_set_context(ctx.id_set()),
            )

            enum_decl = EnumDecl(id, values, id_line, id_col)
            self.state_builder.with_enum_type_decl(enum_decl)

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext) -> None:
            """
            Add new const variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Const_var_declContext): Const variable to add
            """
            node = antlr_get_terminal_node_impl(ctx.ID(0))
            symbol: Token = node.getSymbol()
            id = State._Listener._get_id(node)
            id_line = Some(cast(int, symbol.line))
            id_col = Some(cast(int, symbol.column))

            type_: str = antlr_get_type_from_type_context(ctx)

            node = antlr_get_terminal_node_impl(ctx.ID(1))
            symbol = node.getSymbol()
            init = AllowedValueDecl(
                antlr_get_text(node),
                Some(cast(int, symbol.line)),
                Some(cast(int, symbol.column)),
            )

            const_decl = ConstDecl(id, type_, init, id_line, id_col)
            self.state_builder.with_const_decl(const_decl)

        def exitVar_decl(self, ctx: StateParser.Var_declContext) -> None:
            """
            Add new var variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Var_declContext): Var variable to add
            """
            node = antlr_get_terminal_node_impl(ctx.ID(0))
            symbol: Token = node.getSymbol()
            id: str = State._Listener._get_id(node)
            id_line = Some(cast(int, symbol.line))
            id_col = Some(cast(int, symbol.column))

            type_: str = antlr_get_type_from_type_context(ctx)

            node = antlr_get_terminal_node_impl(ctx.ID(1))
            symbol = node.getSymbol()
            init: AllowedValueDecl = AllowedValueDecl(
                antlr_get_text(node),
                Some(cast(int, symbol.line)),
                Some(cast(int, symbol.column)),
            )

            values: list[AllowedValueDecl] = State._Listener._get_values(
                antlr_get_id_set_context(ctx.id_set()),
            )

            var_decl = VarDecl.var_decl(id, type_, init, values, id_line, id_col)
            if not_(is_successful)(var_decl):
                self.error = Some(var_decl.failure())
                raise Exception()
            self.state_builder.with_var_decl(var_decl.unwrap())

    def __init__(
        self, consts: list[ConstDecl], enums: list[EnumDecl], vars: list[VarDecl]
    ) -> None:
        """
        Initialize State object

        Args:
            consts (list[ConstDecl]): List containing const variable declarations
            enums (list[EnumDecl]): List containing enum variable declarations
            vars (list[VarDecl]): List containing var variable declarations
        """
        self._consts = consts
        self._enums = enums
        self._id2type: Maybe[dict[str, TypeWithDeclLoc]] = Nothing
        self._vars = vars

    def __str__(self) -> str:
        """
        Return string representation of State object
        """
        raise builtins.NotImplementedError("SymbolTable::__str__")

    @staticmethod
    def _build_id_2_type_consts(state: "State") -> Result["State", Error]:
        """
        Adds const variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert state._id2type != Nothing

        id2type = state._id2type.unwrap()
        for const_decl in state._consts:
            if const_decl.id in id2type:
                first = (id2type[const_decl.id]).decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        const_decl.id,
                        const_decl.line,
                        const_decl.col,
                        first.line,
                        first.col,
                    )
                )
            id2type[const_decl.id] = TypeWithDeclLoc(const_decl.type_, const_decl)

        return Success(state)

    @staticmethod
    def _build_id_2_type_enums(state: "State") -> Result["State", Error]:
        """
        Adds enum variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert state._id2type != Nothing

        for i in state._enums:
            result = state._build_id_2_type_enum(i)
            if not_(is_successful)(result):
                return result

        return Success(state)

    @staticmethod
    def _build_id_2_type_vars(state: "State") -> Result["State", Error]:
        """
        Adds var variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert state._id2type != Nothing

        for i in state._vars:
            result = state._build_id_2_type_var(i)
            if not_(is_successful)(result):
                return result

        return Success(state)

    @staticmethod
    def _from_str(context: StateParser.StateContext) -> Result["State", Error]:
        """
        Return a State object from a valid tree, error otherwise

        Args:
            context (StateParser.StateContext): Tree to walk through
        """
        listener = State._Listener()
        try:
            walker: ParseTreeWalker = cast(ParseTreeWalker, ParseTreeWalker.DEFAULT)
            walker.walk(listener, context)
            return listener.state_builder.build()
        except Exception:
            # requires
            assert listener.error != Nothing
            return Failure(listener.error.unwrap())

    @staticmethod
    def _type_check_assigns(
        state: "State", ltype: str, values: Iterable[AllowedValueDecl]
    ) -> Result[tuple[()], Error]:
        """
        Verify all values are of the same type of variable declaration

        Args:
            state (State): State object to retrieve initial type
            ltype (str): Type values should be
            values (Iterable[AllowedValueDecl]): List of values
        """
        # Partial binds variable to the first argument of following function,
        # creating a new function that only requires input for other arguments
        get_type_init = partial(State.get_type, state)
        get_type_assign = partial(typechecking.get_type_assign, ltype)
        for i in values:
            result: Result[str, Error] = flow(
                i.value, get_type_init, bind_result(get_type_assign)
            )
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(())

    @staticmethod
    def _type_check_consts(state: "State") -> Result["State", Error]:
        """
        Verify const variable declarations are type safe

        Args:
            state (State): State object to retrieve initial type
        """
        # Partially bind state to first argument for _type_check_assigns
        type_check_assigns = partial(State._type_check_assigns, state)
        for const_decl in state._consts:
            result = type_check_assigns(const_decl.type_, [const_decl.init])
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(state)

    @staticmethod
    def _type_check_vars(state: "State") -> Result["State", Error]:
        """
        Verify vars variable declarations are type safe

        Args:
            state (State): State object to retrieve initial type
        """
        # Partially bind state to first argument for _type_check_assigns
        type_check_assigns = partial(State._type_check_assigns, state)
        for var_decl in state._vars:
            values = var_decl.values + [var_decl.init]
            result = type_check_assigns(var_decl.type_, values)
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(state)

    @staticmethod
    def type_check(state: "State") -> Result["State", Error]:
        """
        Run the given State object through various tests to make sure all variable declarations are type safe

        Args:
            state (State): State object to run tests through
        """
        # Delete previous dictionary stored in _id2type and initialize it to empty dictionary
        state._id2type = Some(dict())
        result: Result["State", Error] = flow(
            state,
            State._build_id_2_type_enums,
            bind_result(State._build_id_2_type_consts),
            bind_result(State._build_id_2_type_vars),
            bind_result(State._type_check_consts),
            bind_result(State._type_check_vars),
        )

        return result

    def _build_id_2_type_enum(self, enum_decl: EnumDecl) -> Result["State", Error]:
        """
        Ensures that enum variable declarations do not use previously declared variable names

        Args:
            enum_decl (EnumDecl): Enum variable declaration to check
        """
        # requires
        assert self._id2type != Nothing

        id2type = self._id2type.unwrap()
        if enum_decl.id in id2type:
            first = (id2type[enum_decl.id]).decl_loc
            return Failure(
                StateMultipleDefinitionError(
                    enum_decl.id, enum_decl.line, enum_decl.col, first.line, first.col
                )
            )
        id2type[enum_decl.id] = TypeWithDeclLoc(typechecking.ENUM, enum_decl)

        for v in enum_decl.values:
            if v.value in id2type:
                first = id2type[v.value].decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        v.value, v.line, v.col, first.line, first.col
                    )
                )
            else:
                id2type[v.value] = TypeWithDeclLoc(enum_decl.id, v)

        return Success(self)

    def _build_id_2_type_var(self, var_decl: VarDecl) -> Result["State", Error]:
        """
        Ensures that var variable declarations do not use previously declared variable names

        Args:
            VarDecl (VarDecl): Var variable declaration to check
        """
        # requires
        assert self._id2type != Nothing

        id2type = self._id2type.unwrap()
        if var_decl.id in id2type:
            first = (id2type[var_decl.id]).decl_loc
            return Failure(
                StateMultipleDefinitionError(
                    var_decl.id, var_decl.line, var_decl.col, first.line, first.col
                )
            )
        id2type[var_decl.id] = TypeWithDeclLoc(var_decl.type_, var_decl)

        return Success(self)

    def get_type(self, id: str) -> Result[str, Error]:
        """
        Retrieve the type of the variable given the variable name

        Args:
            id (str): Name of the variable
        """
        # requires
        assert self._id2type != Nothing

        id2type = self._id2type.unwrap()
        if id in id2type:
            return Success(id2type[id].type_)
        result: Result[str, Error] = typechecking.get_type_literal(id)
        return result

    def is_defined(self, id: str) -> bool:
        """
        Determines if a variable is defined or not

        Args:
            id (str): Name of variable to check
        """
        # requires
        assert self._id2type != Nothing

        defined: bool = is_successful(self.get_type(id))
        return defined

    @staticmethod
    def from_str(state_def: str) -> Result["State", Error]:
        """
        Interface method used to interact with code outside of the variable declaration checking functionality

        state_def (str): String that contains varaible declarations
        """
        result: Result["State", Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(State._from_str),
        )
        return result
