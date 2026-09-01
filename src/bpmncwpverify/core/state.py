from collections.abc import Iterable
from typing import Any, Protocol, cast

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.Token import Token
from antlr4.tree.Tree import TerminalNode, TerminalNodeImpl
from returns.converters import maybe_to_result
from returns.functions import not_
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.result import Failure, Result, Success, safe

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateListener import StateListener
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.core import typechecking
from bpmncwpverify.core.error import (
    Error,
    NotInitializedError,
    StateAntlrWalkerError,
    StateArraySizeError,
    StateInheritanceError,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
    TypedefPathError,
)


class HasText(Protocol):
    def getText(self) -> str | None: ...


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
    assert node is not None
    assert isinstance(node, TerminalNodeImpl)
    return node


def antlr_get_var_decl(
    node: list[StateParser.Var_declContext] | None,
) -> list[StateParser.Var_declContext]:
    """
    Verifies and returns the node if node is not None, AssertionError otherwise

    Args:
        ctx (StateParser.Var_declContext | None): The node to check if it is not none
    """
    assert node is not None
    return node


def antlr_get_text(node: HasText) -> str:
    """
    Returns the text within the node

    Args:
        ctx (TerminalNodeImpl | StateParser.TypeContext): The node to retrieve the text
    """
    text: str | None = node.getText()
    assert text is not None
    return text


def antlr_get_type_from_type_context(
    ctx: StateParser.Const_var_declContext
    | StateParser.Var_declContext
    | StateParser.Array_declContext,
) -> str:
    """
    Returns the type contained in a Type node

    Args:
        ctx (StateParser.Const_var_declContext | StateParser.Var_declContext | StateParser.Array_declContext): The node to retrieve the type
    """
    if isinstance(ctx, StateParser.Array_declContext):
        type_context = cast(StateParser.Primitive_typeContext, ctx.primitive_type())  # type: ignore[no-untyped-call]
        assert isinstance(type_context, StateParser.Primitive_typeContext)
    else:
        type_context = cast(StateParser.TypeContext, ctx.type_())  # type: ignore[no-untyped-call]
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
        msg = f"line {line}:{column} {msg}"
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
    result: Result[StateParser.StateContext, Error] = safe(parser.state)().alt(
        lambda exc: StateSyntaxError(str(exc))
    )
    return result  # pyright: ignore[reportUnknownVariableType]


class DeclLoc:
    """
    Parent class for all types of variable declarations, stores location of variable declaration
    """

    __slots__ = ["col", "line"]

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

    __slots__ = ["id", "init", "type_"]

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


class ArrayDecl(DeclLoc):
    """
    Represents array variable declaration using keyword array
    """

    __slots__ = ["col", "id", "line", "size", "type_", "values"]

    def __init__(
        self,
        id: str,
        type_: str,
        size: int,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        """
        Initialize ArrayDecl object

        Args:
            id (str): Variable name
            type_ (str): Variable type
            size (int): Array size
            values (list[AllowedValueDecl]): Initial variable values
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        super().__init__(line, col)
        self.id = id
        self.type_ = type_
        self.size = size
        self.values = values

    @staticmethod
    def array_decl(
        id: str,
        type_: str,
        size: int,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> Result["ArrayDecl", Error]:
        """
        Returns an ArrayDecl object if the size of the list is 1 or greater and if init has a length of size, error otherwise

        Args:
            id (str): Variable name
            type_ (str): Variable type
            size (int): Array size
            values (list[AllowedValueDecl]): Initial variable values
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """

        if len(values) != size or size < 1:
            return Failure(StateArraySizeError(id, line, col, size, len(values)))
        return Success(ArrayDecl(id, type_, size, values, line, col))


class VarDecl(DeclLoc):
    """
    Represents variable declaration using keyword var
    """

    __slots__ = ["col", "id", "init", "line", "type_", "values"]

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


class TypeDefDecl(DeclLoc):
    """
    Represents typedef variable declaration using keyword typedef
    """

    __slots__ = ["id", "arrays", "fields", "nested_typedefs", "typedef_inits", "type_"]

    def __init__(
        self,
        id: str,
        arrays: list[ArrayDecl],
        fields: list[VarDecl],
        nested_typedefs: list["TypeDefDecl"],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        """
        Initialize TypeDefDecl object

        Args:
            id (str): Variable name
            arrays (list[ArrayDecl]): List of array declarations
            fields (list[VarDecl]): List of field declarations
            nested_typedefs (list[TypeDefDecl]): List of nested typedef declarations
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        super().__init__(line, col)
        self.id = id
        self.arrays = arrays
        self.fields = fields
        self.nested_typedefs = nested_typedefs

    @staticmethod
    def typedef_decl(
        id: str,
        arrays: list[ArrayDecl],
        fields: list[VarDecl],
        nested_typedefs: list["TypeDefDecl"],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> Result["TypeDefDecl", Error]:
        """
        Returns a TypeDefDecl object

        Args:
            id (str): Variable name
            arrays (list[ArrayDecl]): List of array declarations
            fields (list[VarDecl]): List of field declarations
            nested_typedefs (list[TypeDefDecl]): List of nested typedef declarations
            line (Maybe[int], optional): Possible line number of variable declaration. Defaults to Nothing
            col (Maybe[int], optional): Possible character position in the line of variable declaration. Defaults to Nothing
        """
        return Success(TypeDefDecl(id, arrays, fields, nested_typedefs, line, col))

    def set_id(self, id: str) -> None:
        self.id = id

    def add_array(self, array: ArrayDecl) -> None:
        self.arrays.append(array)

    def add_field(self, field: VarDecl) -> None:
        self.fields.append(field)

    def add_nested_typedef(self, nested_typedef: "TypeDefDecl") -> None:
        self.nested_typedefs.append(nested_typedef)

    def set_line(self, line: Maybe[int]) -> None:
        self.line = line

    def set_col(self, col: Maybe[int]) -> None:
        self.col = col


class TypeWithDeclLoc:
    """
    Stores type related to variable in stored location
    """

    __slots__ = ["decl_loc", "type_"]

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

    __slots__ = ["_arrays", "_consts", "_enums", "_vars", "_typedefs"]

    def __init__(self) -> None:
        """
        Initialize StateBuilder object
        """
        self._consts: list[ConstDecl] = list()
        self._enums: list[EnumDecl] = list()
        self._vars: list[VarDecl] = list()
        self._arrays: list[ArrayDecl] = list()
        self._typedefs: list[TypeDefDecl] = list()

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

    def with_array_decl(self, array_decl: ArrayDecl) -> "StateBuilder":
        """
        Add to list of array variables

        Args:
            array_decl (ArrayDecl): variable to add to list
        """
        self._arrays.append(array_decl)
        return self

    def with_var_decl(self, var_decl: VarDecl) -> "StateBuilder":
        """
        Add to list of var variables

        Args:
            var_decl (VarDecl): variable to add to list
        """
        self._vars.append(var_decl)
        return self

    def with_typedef_decl(self, typedef_decl: TypeDefDecl) -> "StateBuilder":
        """
        Add to list of typedef variables

        Args:
            typedef_decl (TypeDefDecl): variable to add to list
        """
        self._typedefs.append(typedef_decl)
        return self

    def build(self) -> Result["State", Error]:
        """
        Create a State object with the given lists of variables stored within itself
        """
        state = State(
            self._consts, self._enums, self._vars, self._arrays, self._typedefs
        )
        return state.type_check()


class State:
    """
    Verifies variable declaration integrity
    Contains interface method used to interact with code outside of variable declaration checking functionality
    """

    __slots__ = [
        "_arrays",
        "_str2array",
        "_consts",
        "_enums",
        "_id2type",
        "_str2enum",
        "_str2var",
        "_str2const",
        "_vars",
        "_typedefs",
        "_str2typedef",
    ]

    class _Listener(StateListener):
        """
        Adds variables to lists stored in StateBuilder object
        """

        __slots__ = ["state_builder"]

        def __init__(self) -> None:
            """
            Initialize _Listener object
            """
            super().__init__()
            self.state_builder: Result[StateBuilder, Error] = Success(StateBuilder())
            self.typedefStack: list[TypeDefDecl] = []

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
            return AllowedValueDecl(id, Some(symbol.line), Some(symbol.column))

        @staticmethod
        def _get_values(
            ctx: Maybe[StateParser.Id_setContext],
        ) -> list[AllowedValueDecl]:
            """
            Return values from a list of nodes

            Args:
                ctx (Maybe[StateParser.Id_setContext]): Node that contains a list of children to get values from
            """

            def get_value_decls(
                ctx: StateParser.Id_setContext,
            ) -> list[AllowedValueDecl]:
                return [
                    State._Listener._get_value_decl(i)
                    for i in antlr_id_set_context_get_children(ctx)
                ]

            init_list: list[AllowedValueDecl] = list()
            result: list[AllowedValueDecl] = ctx.bind_optional(
                get_value_decls
            ).or_else_call(lambda: init_list)
            return result

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext) -> None:
            """
            Add new enum variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Enum_type_declContext): Enum variable to add
            """

            def get_enum_type_decl() -> EnumDecl:
                node = antlr_get_terminal_node_impl(ctx.ID())  # type: ignore[no-untyped-call]
                symbol: Token = node.getSymbol()
                id: str = State._Listener._get_id(node)
                id_line = Some(symbol.line)
                id_col = Some(symbol.column)

                values: list[AllowedValueDecl] = State._Listener._get_values(
                    antlr_get_id_set_context(ctx.id_set()),  # type: ignore[no-untyped-call]
                )

                return EnumDecl(id, values, id_line, id_col)

            self.state_builder = self.state_builder.map(
                lambda builder: builder.with_enum_type_decl(get_enum_type_decl())
            )

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext) -> None:
            """
            Add new const variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Const_var_declContext): Const variable to add
            """

            def get_const_var_decl() -> ConstDecl:
                node = antlr_get_terminal_node_impl(ctx.ID(0))
                symbol: Token = node.getSymbol()
                id = State._Listener._get_id(node)
                id_line = Some(symbol.line)
                id_col = Some(symbol.column)

                type_: str = antlr_get_type_from_type_context(ctx)

                node = antlr_get_terminal_node_impl(ctx.ID(1))
                symbol = node.getSymbol()
                init = AllowedValueDecl(
                    antlr_get_text(node),
                    Some(symbol.line),
                    Some(symbol.column),
                )

                return ConstDecl(id, type_, init, id_line, id_col)

            self.state_builder = self.state_builder.map(
                lambda builder: builder.with_const_decl(get_const_var_decl())
            )

        def exitVar_decl(self, ctx: StateParser.Var_declContext) -> None:
            """
            Add new var variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Var_declContext): Var variable to add
            """

            def attach_var_decl_to_typedef(var_decl: VarDecl) -> Result[VarDecl, Error]:
                if not self.typedefStack:
                    return Failure(TypedefPathError(var_decl.id))
                self.typedefStack[-1].add_field(var_decl)
                return Success(var_decl)

            def get_var_decl(builder: StateBuilder) -> Result[StateBuilder, Error]:
                node = antlr_get_terminal_node_impl(ctx.ID(0))
                symbol: Token = node.getSymbol()
                id: str = State._Listener._get_id(node)
                id_line = Some(symbol.line)
                id_col = Some(symbol.column)

                type_: str = antlr_get_type_from_type_context(ctx)

                node = antlr_get_terminal_node_impl(ctx.ID(1))
                symbol = node.getSymbol()
                init: AllowedValueDecl = AllowedValueDecl(
                    antlr_get_text(node),
                    Some(symbol.line),
                    Some(symbol.column),
                )

                values: list[AllowedValueDecl] = State._Listener._get_values(
                    antlr_get_id_set_context(ctx.id_set()),  # type: ignore[no-untyped-call]
                )

                result = VarDecl.var_decl(id, type_, init, values, id_line, id_col)

                if (
                    ctx.parentCtx is not None
                    and ctx.parentCtx.parentCtx is not None
                    and isinstance(
                        ctx.parentCtx.parentCtx, StateParser.Typedef_declContext
                    )
                ):
                    result.bind_result(attach_var_decl_to_typedef)
                    return result.map(lambda _: builder).alt(lambda error: error)
                else:
                    return result.map(builder.with_var_decl).alt(lambda error: error)

            self.state_builder = self.state_builder.bind(get_var_decl)  # pyright: ignore[reportUnknownMemberType]

        def exitArray_decl(self, ctx: StateParser.Array_declContext) -> None:
            """
            Add new array variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Array_declContext): Array variable to add
            """

            def attach_array_decl_to_typedef(
                array_decl: ArrayDecl,
            ) -> Result[ArrayDecl, Error]:
                if not self.typedefStack:
                    return Failure(TypedefPathError(array_decl.id))
                self.typedefStack[-1].add_array(array_decl)
                return Success(array_decl)

            def get_array_decl(builder: StateBuilder) -> Result[StateBuilder, Error]:
                node = antlr_get_terminal_node_impl(ctx.ID(0))
                symbol: Token = node.getSymbol()
                id: str = State._Listener._get_id(node)
                id_line = Some(symbol.line)
                id_col = Some(symbol.column)

                type_: str = antlr_get_type_from_type_context(ctx)

                number_node: TerminalNode = antlr_get_terminal_node_impl(ctx.ID(1))
                size: int = int(antlr_get_text(number_node))

                values: list[AllowedValueDecl] = State._Listener._get_values(
                    antlr_get_id_set_context(ctx.id_set()),  # type: ignore[no-untyped-call]
                )

                result = ArrayDecl.array_decl(id, type_, size, values, id_line, id_col)
                if (
                    ctx.parentCtx is not None
                    and ctx.parentCtx.parentCtx is not None
                    and isinstance(
                        ctx.parentCtx.parentCtx, StateParser.Typedef_declContext
                    )
                ):
                    result.bind_result(attach_array_decl_to_typedef)
                    return result.map(lambda _: builder).alt(lambda error: error)
                else:
                    return result.map(builder.with_array_decl).alt(lambda error: error)

            self.state_builder = self.state_builder.bind(get_array_decl)  # pyright: ignore[reportUnknownMemberType]

        def enterTypedef_decl(self, ctx: StateParser.Typedef_declContext) -> None:
            """
            Add new typedef variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Typedef_declContext): Typedef variable to add
            """
            self.typedefStack.append(TypeDefDecl("", [], [], []))

        def exitTypedef_decl(self, ctx: StateParser.Typedef_declContext) -> None:
            """
            Add new typedef variable to the list stored in StateBuilder object

            Args:
                ctx (StateParser.Typedef_declContext): Typedef variable to add
            """

            def result_or_error(typeDefDecl: TypeDefDecl) -> Result[TypeDefDecl, Error]:
                try:
                    return Success(self.typedefStack.pop())
                except IndexError:
                    return Failure(TypedefPathError("Index Error at " + typeDefDecl.id))

            def get_typedef_decl(builder: StateBuilder) -> Result[StateBuilder, Error]:
                node = antlr_get_terminal_node_impl(ctx.ID())  # type: ignore[no-untyped-call]
                symbol: Token = node.getSymbol()
                id: str = State._Listener._get_id(node)
                self.typedefStack[-1].set_id(id)

                id_line = Some(symbol.line)
                id_col = Some(symbol.column)
                self.typedefStack[-1].set_line(id_line)
                self.typedefStack[-1].set_col(id_col)

                if ctx.parentCtx is not None and isinstance(
                    ctx.parentCtx, StateParser.Typedef_decl_setContext
                ):
                    self.typedefStack[-2].add_nested_typedef(self.typedefStack[-1])

                result = result_or_error(self.typedefStack[-1])
                return result.map(builder.with_typedef_decl).alt(lambda error: error)

            self.state_builder = self.state_builder.bind(get_typedef_decl)  # pyright: ignore[reportUnknownMemberType]

    def __init__(
        self,
        consts: list[ConstDecl],
        enums: list[EnumDecl],
        vars: list[VarDecl],
        arrays: list[ArrayDecl],
        typedefs: list[TypeDefDecl],
    ) -> None:
        """
        Initialize State object

        Args:
            consts (list[ConstDecl]): List containing const variable declarations
            enums (list[EnumDecl]): List containing enum variable declarations
            vars (list[VarDecl]): List containing var variable declarations
            arrays (list[ArrayDecl]): List containing array variable declarations
            typedefs (list[TypeDefDecl]): List containing typedef variable declarations
        """
        self._consts = consts
        self._enums = enums
        self._vars = vars
        self._arrays = arrays
        self._typedefs = typedefs
        self._id2type: Maybe[dict[str, TypeWithDeclLoc]] = Nothing
        self._str2var: Maybe[dict[str, VarDecl]] = Nothing
        self._str2enum: Maybe[dict[str, EnumDecl]] = Nothing
        self._str2const: Maybe[dict[str, ConstDecl]] = Nothing
        self._str2array: Maybe[dict[str, ArrayDecl]] = Nothing
        self._str2typedef: Maybe[dict[str, TypeDefDecl]] = Nothing

    @staticmethod
    def _enums_to_str(enums: list[EnumDecl]) -> str:
        """
        Return string representation of list of EnumDecl objects

        Args:
            enums (list[EnumDecl]): List of EnumDecl objects to convert to string
        """
        state_str = ""
        for enum in enums:
            state_str += "enum " + enum.id + " {"
            for vals in range(len(enum.values)):
                if vals == 0:
                    state_str += enum.values[vals].value
                    continue
                state_str += " " + enum.values[vals].value
            state_str += "}\n"
        return state_str

    @staticmethod
    def _arrays_to_str(arrays: list[ArrayDecl]) -> str:
        """
        Return string representation of list of ArrayDecl objects

        Args:
            arrays (list[ArrayDecl]): List of ArrayDecl objects to convert to string
        """
        state_str = ""
        for array in arrays:
            state_str += (
                "array "
                + array.id
                + " "
                + array.type_
                + "["
                + str(array.size)
                + "] = \n[\n"
                + ": "
            )
            for val in array.values:
                state_str += "  " + val.value + "\n"
            state_str += "]\n"
        return state_str

    @staticmethod
    def _consts_to_str(consts: list[ConstDecl]) -> str:
        """
        Return string representation of list of ConstDecl objects

        Args:
            consts (list[ConstDecl]): List of ConstDecl objects to convert to string
        """
        state_str = ""
        for const in consts:
            state_str += (
                "const "
                + const.id
                + ": "
                + const.type_
                + " = "
                + const.init.value
                + "\n"
            )
        return state_str

    @staticmethod
    def _vars_to_str(vars: list[VarDecl]) -> str:
        """
        Return string representation of list of VarDecl objects

        Args:
            vars (list[VarDecl]): List of VarDecl objects to convert to string
        """
        state_str = ""
        for var in vars:
            state_str += "var " + var.id + " : " + var.type_ + " = " + var.init.value
            if len(var.values) != 0:
                state_str += " {"
                for vals in range(len(var.values)):
                    if vals == 0:
                        state_str += var.values[vals].value
                        continue
                    state_str += " " + var.values[vals].value
                state_str += "}\n"
            else:
                state_str += "\n"
        return state_str

    @staticmethod
    def _typedefs_to_str(typedefs: list[TypeDefDecl]) -> str:
        """
        Return string representation of list of TypeDefDecl objects

        Args:
            typedefs (list[TypeDefDecl]): List of TypeDefDecl objects to convert to string
        """
        state_str = ""
        for typedef in typedefs:
            state_str += "typedef " + typedef.id + " {\n"
            state_str += State._vars_to_str(typedef.fields)
            state_str += State._typedefs_to_str(typedef.nested_typedefs)
            state_str += "}\n"
        return state_str

    def __str__(self) -> str:
        """
        Return string representation of State object
        """
        state_str = ""
        state_str += State._enums_to_str(self._enums)
        state_str += State._consts_to_str(self._consts)
        state_str += State._vars_to_str(self._vars)
        state_str += State._arrays_to_str(self._arrays)
        state_str += State._typedefs_to_str(self._typedefs)
        return state_str

    @property
    def consts(self) -> tuple[ConstDecl, ...]:
        return tuple(self._consts)

    @property
    def enums(self) -> tuple[EnumDecl, ...]:
        return tuple(self._enums)

    @property
    def typedefs(self) -> tuple[TypeDefDecl, ...]:
        return tuple(self._typedefs)

    @property
    def vars(self) -> tuple[VarDecl, ...]:
        return tuple(self._vars)

    @property
    def arrays(self) -> tuple[ArrayDecl, ...]:
        return tuple(self._arrays)

    @property
    def str2var(self) -> dict[str, VarDecl]:
        return self._str2var.value_or({})

    @property
    def str2array(self) -> dict[str, ArrayDecl]:
        return self._str2array.value_or({})

    def is_variable(self, variable: str) -> bool:
        return self._str2var.map(lambda d: variable in d).value_or(False)

    def is_enum(self, variable: str) -> bool:
        return self._str2enum.map(lambda d: variable in d).value_or(False)

    def is_constant(self, variable: str) -> bool:
        return self._str2const.map(lambda d: variable in d).value_or(False)

    def is_array(self, variable: str) -> bool:
        return self._str2array.map(lambda d: variable in d).value_or(False)

    def is_typedef(self, variable: str) -> bool:
        return self._str2typedef.map(lambda d: variable in d).value_or(False)

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

    def get_type(self, id: str) -> Result[str, Error]:
        """
        Retrieve the type of the variable given the variable name

        Args:
            id (str): Name of the variable
        """

        def _lookup(id2type: dict[str, TypeWithDeclLoc]) -> Result[str, Error]:
            if id in id2type:
                return Success(id2type[id].type_)
            elif "." in id:
                return Failure(TypedefPathError(id))
            else:
                return typechecking.get_type_literal(id)

        return maybe_to_result(self._id2type, Error()).bind(_lookup)  # pyright: ignore[reportUnknownMemberType]

    def type_check(self) -> Result["State", Error]:
        """
        Run the given State object through various tests to make sure all variable declarations are type safe
        """
        self._id2type = Some(dict())
        self._str2var = Some(dict())
        self._str2enum = Some(dict())
        self._str2const = Some(dict())
        self._str2array = Some(dict())
        self._str2typedef = Some(dict())
        result: Result[State, Error] = (
            self._build_id_2_type_enums()  # pyright: ignore[reportUnknownMemberType]
            .bind(lambda _: self._build_id_2_type_consts())
            .bind(lambda _: self._build_id_2_type_typedefs())
            .bind(lambda _: self._build_id_2_type_vars())
            .bind(lambda _: self._build_id_2_type_arrays())
            .bind(lambda _: self._type_check_consts())
            .bind(lambda _: self._type_check_vars())
            .bind(lambda _: self._type_check_arrays())
            .bind(lambda _: self._type_check_typedefs())
            .bind(lambda _: self._build_typedef_paths())
            .map(lambda _: self)
        )
        return result

    def _build_id_2_type_consts(self) -> Result[None, Error]:
        """
        Adds const variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice
        """

        def _find(
            id2type: dict[str, TypeWithDeclLoc], str2const: dict[str, ConstDecl]
        ) -> Result[None, Error]:
            for const_decl in self._consts:
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
                str2const[const_decl.id] = const_decl
            return Success(None)

        return maybe_to_result(self._id2type, Error()).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda id2type: maybe_to_result(self._str2const, Error()).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda str2const: _find(id2type, str2const)
            )
        )

    def _build_id_2_type_enums(self) -> Result[None, Error]:
        """
        Adds enum variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert self._id2type != Nothing

        for i in self._enums:
            result = self._build_id_2_type_enum(i)
            if not_(is_successful)(result):
                return result

        return Success(None)

    def _build_id_2_type_vars(self) -> Result[None, Error]:
        """
        Adds var variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert self._id2type != Nothing

        for i in self._vars:
            result = self._build_id_2_type_var(i)
            if not_(is_successful)(result):
                return result

        return Success(None)

    def _build_id_2_type_arrays(self) -> Result[None, Error]:
        """
        Adds array variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert self._id2type != Nothing

        for i in self._arrays:
            result = self._build_id_2_type_array(i)
            if not_(is_successful)(result):
                return result

        return Success(None)

    def _build_id_2_type_typedefs(self) -> Result[None, Error]:
        """
        Adds typedef variables into id2type dictionary
        Verifies there are no two variables with the same name being declared twice

        Args:
            state (State): State object to modify
        """
        # requires
        assert self._id2type != Nothing
        # ensures that all typedefs are properly initialized.

        for i in self._typedefs:
            result = self._build_id_2_type_typedef(i)
            if not_(is_successful)(result):
                return result

        return Success(None)

    def _type_check_assigns(
        self, ltype: str, values: Iterable[AllowedValueDecl]
    ) -> Result[None, Error]:
        """
        Verify all values are of the same type of variable declaration

        Args:
            state (State): State object to retrieve initial type
            ltype (str): Type values should be
            values (Iterable[AllowedValueDecl]): List of values
        """
        for i in values:
            result: Result[str, Error] = self.get_type(i.value).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda rtype: typechecking.get_type_assign(ltype, rtype)
            )
            if not_(is_successful)(result):
                return cast(Result[None, Error], result)
        return Success(None)

    def _type_check_consts(self) -> Result[None, Error]:
        """
        Verify const variable declarations are type safe

        Args:
            state (State): State object to retrieve initial type
        """
        for const_decl in self._consts:
            result = self._type_check_assigns(const_decl.type_, [const_decl.init])
            if not_(is_successful)(result):
                return result
        return Success(None)

    def _type_check_vars(self) -> Result[None, Error]:
        """
        Verify vars variable declarations are type safe

        Args:
            state (State): State object to retrieve initial type
        """
        for var_decl in self._vars:
            values = var_decl.values + [var_decl.init]
            result = self._type_check_assigns(var_decl.type_, values)
            if not_(is_successful)(result):
                return result
        return Success(None)

    def _type_check_arrays(self) -> Result[None, Error]:
        """
        Verify array variable declarations are type safe

        Args:
            state (State): State object to retrieve initial type
        """
        for array_decl in self._arrays:
            values = array_decl.values
            result = self._type_check_assigns(array_decl.type_, values)
            if not_(is_successful)(result):
                return result
        return Success(None)

    def _type_check_typedefs(self) -> Result[None, Error]:
        """
        Verify typedef variable declarations are type safe, including nested variable declarations

        Args:
            state (State): State object to retrieve initial type
        """

        def _type_check_typedef(typedef_decl: TypeDefDecl) -> Result[None, Error]:
            for var_decl in typedef_decl.fields:
                values = var_decl.values + [var_decl.init]
                result = self._type_check_assigns(var_decl.type_, values)
                if not_(is_successful)(result):
                    return result
            for array_decl in typedef_decl.arrays:
                values = array_decl.values
                result = self._type_check_assigns(array_decl.type_, values)
                if not_(is_successful)(result):
                    return result
            for nested_typedef in typedef_decl.nested_typedefs:
                result = _type_check_typedef(nested_typedef)
                if not_(is_successful)(result):
                    return result
            return Success(None)

        for typedef_decl in self._typedefs:
            result = _type_check_typedef(typedef_decl)
            if not_(is_successful)(result):
                return result
        return Success(None)

    def _build_id_2_type_enum(self, enum_decl: EnumDecl) -> Result[None, Error]:
        """
        Ensures that enum variable declarations do not use previously declared variable names

        Args:
            enum_decl (EnumDecl): Enum variable declaration to check
        """

        def _find(
            id2type: dict[str, TypeWithDeclLoc], str2enum: dict[str, EnumDecl]
        ) -> Result[None, Error]:
            if enum_decl.id in id2type:
                first = id2type[enum_decl.id].decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        enum_decl.id,
                        enum_decl.line,
                        enum_decl.col,
                        first.line,
                        first.col,
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
                id2type[v.value] = TypeWithDeclLoc(enum_decl.id, v)
                str2enum[v.value] = enum_decl

            return Success(None)

        return maybe_to_result(self._id2type, Error()).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda id2type: maybe_to_result(self._str2enum, Error()).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda str2enum: _find(id2type, str2enum)
            )
        )

    def _build_typedef_paths(self) -> Result[None, Error]:
        def _build_paths(str2typedef: dict[str, TypeDefDecl]) -> Result[None, Error]:
            for var_decl in self._vars:
                if var_decl.type_ != typechecking.TYPEDEF:
                    continue
                if var_decl.init.value not in str2typedef:
                    return Failure(
                        StateInheritanceError(
                            var_decl.id,
                            var_decl.init.value,
                            var_decl.line,
                            var_decl.col,
                        )
                    )

                result = self._build_typedef_path(
                    var_decl.id, str2typedef[var_decl.init.value]
                )
                if not_(is_successful)(result):
                    return result
            return Success(None)

        return maybe_to_result(
            self._str2typedef, NotInitializedError("_str2typedef")
        ).bind(  # pyright: ignore[reportUnknownMemberType]
            _build_paths  # type: ignore[arg-type] # pyright: ignore[reportUnknownMemberType]
        )

    def _build_typedef_path(
        self, id: str, typedef_decl: TypeDefDecl
    ) -> Result[None, Error]:
        """
        Builds the paths for each field in a typedef declaration.

        Args:
            id (str): The ID of the var
            typedef_decl (TypeDefDecl): Typedef variable declaration to build paths for
        """

        def _check_vars_and_arrays(
            id2type: dict[str, TypeWithDeclLoc],
            str2var: dict[str, VarDecl],
            str2array: dict[str, ArrayDecl],
        ) -> Result[None, Error]:
            for var_decl in typedef_decl.fields:
                if var_decl.type_ == typechecking.TYPEDEF:
                    nested_path = f"{id}.{var_decl.id}"
                    nested_typedef_decl = next(
                        (
                            td
                            for td in typedef_decl.nested_typedefs
                            if td.id == var_decl.init.value
                        ),
                        None,
                    )
                    if nested_typedef_decl is None:
                        return Failure(
                            StateInheritanceError(
                                nested_path,
                                var_decl.init.value,
                                var_decl.line,
                                var_decl.col,
                            )
                        )
                    result = self._build_typedef_path(nested_path, nested_typedef_decl)
                    if not_(is_successful)(result):
                        return result
                else:
                    full_path = f"{id}.{var_decl.id}"
                    id2type[full_path] = TypeWithDeclLoc(var_decl.type_, var_decl)
                    str2var[full_path] = var_decl
            for array_decl in typedef_decl.arrays:
                full_path = f"{id}.{array_decl.id}"
                id2type[full_path] = TypeWithDeclLoc(array_decl.type_, array_decl)
                str2array[full_path] = array_decl
            return Success(None)

        return maybe_to_result(self._id2type, NotInitializedError("_id2type")).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda id2type: maybe_to_result(
                self._str2var, NotInitializedError("_str2var")
            ).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda str2var: maybe_to_result(
                    self._str2array, NotInitializedError("_str2array")
                ).bind(  # pyright: ignore[reportUnknownMemberType]
                    lambda str2array: _check_vars_and_arrays(  # type: ignore[return-value, arg-type] # pyright: ignore[reportArgumentType]
                        id2type, str2var, str2array
                    )
                )
            )
        )

    def _build_id_2_type_var(self, var_decl: VarDecl) -> Result[None, Error]:
        """
        Ensures that var variable declarations do not use previously declared variable names

        Args:
            VarDecl (VarDecl): Var variable declaration to check
        """

        def _find(
            id2type: dict[str, TypeWithDeclLoc], str2var: dict[str, VarDecl]
        ) -> Result[None, Error]:
            if var_decl.id in id2type:
                first = (id2type[var_decl.id]).decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        var_decl.id, var_decl.line, var_decl.col, first.line, first.col
                    )
                )
            id2type[var_decl.id] = TypeWithDeclLoc(var_decl.type_, var_decl)
            str2var[var_decl.id] = var_decl
            return Success(None)

        return maybe_to_result(self._id2type, Error()).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda id2type: maybe_to_result(self._str2var, Error()).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda str2var: _find(id2type, str2var)
            )
        )

    def _build_id_2_type_typedef(
        self, typedef_decl: TypeDefDecl
    ) -> Result[None, Error]:
        """
        Ensures that typedef variable declarations do not use previously declared variable names

        Args:
            typedef_decl (TypeDefDecl): Typedef variable declaration to check
        """

        def _check_duplicate_typedef(
            id2type: dict[str, TypeWithDeclLoc], str2typedef: dict[str, TypeDefDecl]
        ) -> Result[None, Error]:
            # check for duplicate typedef name in global declarations
            if typedef_decl.id in id2type:
                first = (id2type[typedef_decl.id]).decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        typedef_decl.id,
                        typedef_decl.line,
                        typedef_decl.col,
                        first.line,
                        first.col,
                    )
                )
            # add the typedef to the id2type and str2typedef dictionaries
            id2type[typedef_decl.id] = TypeWithDeclLoc(
                typechecking.TYPEDEF, typedef_decl
            )
            str2typedef[typedef_decl.id] = typedef_decl
            return Success(None)

        def _check_duplicate_arrays() -> Result[None, Error]:
            # check inside the typedef for duplicate array names
            array_names = [array_decl.id for array_decl in typedef_decl.arrays]
            for array_decl in typedef_decl.arrays:
                if array_names.count(array_decl.id) != 1:
                    return Failure(
                        StateMultipleDefinitionError(
                            array_decl.id,
                            typedef_decl.line,
                            typedef_decl.col,
                            array_decl.line,
                            array_decl.col,
                        )
                    )
            return Success(None)

        def _check_duplicate_fields() -> Result[None, Error]:
            # check inside the typedef for duplicate field names
            field_names = [var_decl.id for var_decl in typedef_decl.fields]
            for var_decl in typedef_decl.fields:
                if field_names.count(var_decl.id) != 1:
                    return Failure(
                        StateMultipleDefinitionError(
                            var_decl.id,
                            typedef_decl.line,
                            typedef_decl.col,
                            var_decl.line,
                            var_decl.col,
                        )
                    )
            return Success(None)

        return maybe_to_result(self._id2type, NotInitializedError("_id2type")).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda id2type: maybe_to_result(
                self._str2typedef, NotInitializedError("_str2typedef")
            ).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda str2typedef: _check_duplicate_typedef(id2type, str2typedef).bind(  # type: ignore[return-value, arg-type] # pyright: ignore[reportArgumentType, reportUnknownMemberType]
                    lambda _: _check_duplicate_fields().bind(  # pyright: ignore[reportArgumentType, reportUnknownMemberType]
                        lambda _: _check_duplicate_arrays()
                    )
                )
            )
        )

    def _build_id_2_type_array(self, array_decl: ArrayDecl) -> Result[None, Error]:
        """
        Ensures that array variable declarations do not use previously declared variable names

        Args:
            array_decl (ArrayDecl): Array variable declaration to check
        """
        result_id_2_type = cast(
            "Result[dict[str, TypeWithDeclLoc], Error]",
            maybe_to_result(self._id2type, NotInitializedError("_id2type")),
        )

        result_str_2_array = cast(
            "Result[dict[str, ArrayDecl], Error]",
            maybe_to_result(self._str2array, NotInitializedError("_str2array")),
        )

        def insert(
            id2type: dict[str, TypeWithDeclLoc], str2array: dict[str, ArrayDecl]
        ) -> Result[None, Error]:
            if array_decl.id in id2type:
                first = id2type[array_decl.id].decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        array_decl.id,
                        array_decl.line,
                        array_decl.col,
                        first.line,
                        first.col,
                    )
                )
            id2type[array_decl.id] = TypeWithDeclLoc(typechecking.ARRAY, array_decl)
            str2array[array_decl.id] = array_decl

            return Success(None)

        return result_id_2_type.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda id2type: result_str_2_array.bind(  # pyright: ignore[reportUnknownMemberType]
                lambda str2array: insert(id2type, str2array)
            )
        )

    @staticmethod
    def from_str(state_def: str) -> Result["State", Error]:
        """
        Interface method used to interact with code outside of the variable declaration checking functionality

        state_def (str): String that contains varaible declarations
        """
        result: Result[State, Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(State._from_str),
        )
        return result

    @staticmethod
    def _from_str(context: StateParser.StateContext) -> Result["State", Error]:
        """
        Return a State object from a valid tree, error otherwise

        Args:
            context (StateParser.StateContext): Tree to walk through
        """

        @safe
        def walk_tree() -> State._Listener:
            walker: ParseTreeWalker = ParseTreeWalker.DEFAULT
            listener = State._Listener()
            walker.walk(listener, context)
            return listener

        listner_result: Result[State._Listener, Error] = walk_tree().alt(
            lambda exc: StateAntlrWalkerError(str(exc))
        )
        return listner_result.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda listener: listener.state_builder.bind(  # pyright: ignore[reportArgumentType, reportUnknownMemberType]
                lambda builder: builder.build()
            )
        )
