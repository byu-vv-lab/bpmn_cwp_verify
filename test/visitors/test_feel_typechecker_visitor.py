import pytest

from bpmncwpverify.core.error import (
    ErrorException,
    ExpressionComputationCompatabilityError,
    ExpressionIfBranchCompatabilityError,
    ExpressionLogicalCompatibilityError,
    ExpressionOutOfScope,
    ExpressionRelationalNotError,
    ExpressionRelationCompatabilityError,
    ExpressionTripleInputError,
    ExpressionUnrecognizedID,
    TypingAssignCompatabilityError,
    TypingListCompatibiltiyError,
    TypingListOfExpressionsError,
    TypingNoTypeError,
    TypingTripleVariableError,
)
from bpmncwpverify.core.feel_tree import (
    AddNode,
    BoolLiteralNode,
    ChooseNode,
    ComparisonOperatorNode,
    ConditionalOperatorNode,
    EqualNode,
    IfNode,
    ListNode,
    NotNode,
    NumberLiteralNode,
    QualifiedNameNode,
    TripleListNode,
    TripleNode,
)
from bpmncwpverify.core.state import (
    AllowedValueDecl,
    EnumDecl,
    State,
    StateBuilder,
    VarDecl,
)
from bpmncwpverify.core.typechecking import (
    BIT,
    BOOL,
    BYTE,
    INT,
)
from bpmncwpverify.visitors.feel_typechecker_visitor import TypeCheckerVisitor


def test_byte_number_literal() -> None:
    node = NumberLiteralNode("45")
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_decimal_number_literal() -> None:
    node = NumberLiteralNode("1.5")
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, TypingNoTypeError)
    assert error.value.error.id == "1.5"


def test_int_number_literal() -> None:
    node = NumberLiteralNode("100000")
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == INT


def test_bit_number_literal() -> None:
    node = NumberLiteralNode("0")
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BIT


def test_bool_boolean_literal() -> None:
    node = BoolLiteralNode("true")
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BOOL


def test_qualified_name_literal_good() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "blackbox",
            "bit",
            [AllowedValueDecl("1"), AllowedValueDecl("0")],
        )
    )
    state = builder.build().unwrap()
    node = QualifiedNameNode("blackbox")
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BIT


def test_qualified_name_literal_not_recongnized_name() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "foo",
            "bit",
            [AllowedValueDecl("1"), AllowedValueDecl("0")],
        )
    )
    state = builder.build().unwrap()
    node = QualifiedNameNode("blackbox")
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionUnrecognizedID)
    assert error.value.error.id == "blackbox"


def test_qualified_name_literal_enum_type_not_variable() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "x",
            "bit",
            [AllowedValueDecl("1"), AllowedValueDecl("0")],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "blackboxState", [AllowedValueDecl("missing"), AllowedValueDecl("found")]
        )
    )
    state = builder.build().unwrap()
    node = QualifiedNameNode("blackboxState")
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionUnrecognizedID)
    assert error.value.error.id == "blackboxState"


def test_list_of_number_literals() -> None:
    node = ListNode(
        [NumberLiteralNode("2"), NumberLiteralNode("3"), NumberLiteralNode("4")]
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_list_empty() -> None:
    node = ListNode([])
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == "None"


def test_list_of_number_literals_not_same_type() -> None:
    node = ListNode(
        [NumberLiteralNode("1"), NumberLiteralNode("2"), NumberLiteralNode("3")]
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_list_of_bool_and_number_literals() -> None:
    node = ListNode(
        [BoolLiteralNode("true"), NumberLiteralNode("2"), NumberLiteralNode("3")]
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, TypingListCompatibiltiyError)
    assert error.value.error.first_type == BOOL
    assert error.value.error.second_type == BYTE


def test_list_of_none_leaf_nodes() -> None:
    node = ListNode(
        [
            ListNode([NumberLiteralNode("2")]),
            NumberLiteralNode("3"),
            NumberLiteralNode("4"),
        ]
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, TypingListOfExpressionsError)


def test_binary_add_2_bytes() -> None:
    node = AddNode(NumberLiteralNode("2"), NumberLiteralNode("2"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_binary_add_bool_byte() -> None:
    node = AddNode(BoolLiteralNode("false"), NumberLiteralNode("2"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionComputationCompatabilityError)
    assert error.value.error.ltype == BOOL
    assert error.value.error.rtype == BYTE


def test_binary_add_bit_byte() -> None:
    node = AddNode(NumberLiteralNode("0"), NumberLiteralNode("2"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_binary_add_qualified_name_byte_with_byte() -> None:
    builder = StateBuilder()
    builder.with_var_decl(VarDecl("x", "byte", []))
    state = builder.build().unwrap()
    node = AddNode(QualifiedNameNode("x"), NumberLiteralNode("2"))
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)

    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_comparision_bit_and_bit() -> None:
    node = ComparisonOperatorNode(NumberLiteralNode("0"), NumberLiteralNode("1"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BOOL


def test_comparision_byte_and_byte() -> None:
    node = ComparisonOperatorNode(NumberLiteralNode("3"), NumberLiteralNode("2"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BOOL


def test_comparision_bit_and_byte() -> None:
    node = ComparisonOperatorNode(NumberLiteralNode("0"), NumberLiteralNode("2"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BOOL


def test_comparision_bool_and_byte() -> None:
    node = ComparisonOperatorNode(BoolLiteralNode("true"), NumberLiteralNode("2"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionRelationCompatabilityError)
    assert error.value.error.ltype == BOOL
    assert error.value.error.rtype == BYTE


def test_conditional_bool_and_bool() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "y",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = ConditionalOperatorNode(QualifiedNameNode("y"), BoolLiteralNode("true"))
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BOOL


def test_conditional_bit_and_bit() -> None:
    node = ConditionalOperatorNode(NumberLiteralNode("1"), NumberLiteralNode("0"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionLogicalCompatibilityError)
    assert error.value.error.ltype == BIT
    assert error.value.error.rtype == BIT


def test_conditional_bool_and_bit() -> None:
    node = ConditionalOperatorNode(BoolLiteralNode("false"), NumberLiteralNode("0"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionLogicalCompatibilityError)
    assert error.value.error.ltype == BOOL
    assert error.value.error.rtype == BIT


def test_conditional_bit_and_byte() -> None:
    node = ConditionalOperatorNode(NumberLiteralNode("1"), NumberLiteralNode("42"))
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionLogicalCompatibilityError)
    assert error.value.error.ltype == BIT
    assert error.value.error.rtype == BYTE


def test_conditional_not_with_bools() -> None:
    node = ConditionalOperatorNode(
        BoolLiteralNode("true"), NotNode(BoolLiteralNode("false"))
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BOOL


def test_conditional_not_with_bool_and_bit() -> None:
    node = ConditionalOperatorNode(
        BoolLiteralNode("true"), NotNode(NumberLiteralNode("0"))
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionRelationalNotError)
    assert error.value.error.type == BIT


def test_if_true_bit_and_bit() -> None:
    node = IfNode(
        BoolLiteralNode("true"), NumberLiteralNode("1"), NumberLiteralNode("0")
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BIT


def test_if_true_byte_and_byte() -> None:
    node = IfNode(
        BoolLiteralNode("false"), NumberLiteralNode("42"), NumberLiteralNode("43")
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_if_true_bit_and_byte() -> None:
    node = IfNode(
        BoolLiteralNode("false"), NumberLiteralNode("1"), NumberLiteralNode("42")
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_if_true_bool_bit() -> None:
    node = IfNode(
        BoolLiteralNode("false"), BoolLiteralNode("true"), NumberLiteralNode("0")
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionIfBranchCompatabilityError)
    assert error.value.error.thentype == "bool"
    assert error.value.error.elsetype == "bit"


def test_if_x_x_and_bit() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "x",
            "bit",
            [AllowedValueDecl("1"), AllowedValueDecl("0")],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "y",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = IfNode(
        QualifiedNameNode("y"), QualifiedNameNode("x"), NumberLiteralNode("0")
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BIT


def test_choose() -> None:
    node = ChooseNode(
        ListNode(
            [NumberLiteralNode("3"), NumberLiteralNode("4"), NumberLiteralNode("5")]
        )
    )
    state = State([], [], [], [])
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_choose_enums() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [AllowedValueDecl("waiting"), AllowedValueDecl("off")],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    state = builder.build().unwrap()
    node = ChooseNode(
        ListNode([QualifiedNameNode("standby"), QualifiedNameNode("waiting")])
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == "commsState"


def test_triple() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "byte",
            [AllowedValueDecl("2"), AllowedValueDecl("3")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([]),
        IfNode(BoolLiteralNode("true"), NumberLiteralNode("2"), NumberLiteralNode("3")),
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == BYTE


def test_triple_bool_input() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "byte",
            [AllowedValueDecl("2"), AllowedValueDecl("3")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([BoolLiteralNode("true")]),
        IfNode(BoolLiteralNode("true"), NumberLiteralNode("2"), NumberLiteralNode("3")),
    )
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionTripleInputError)


def test_triple_with_one_input() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
                AllowedValueDecl("standby"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "deployed",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([QualifiedNameNode("deployed")]),
        IfNode(
            QualifiedNameNode("deployed"),
            ChooseNode(
                ListNode([QualifiedNameNode("off"), QualifiedNameNode("waiting")])
            ),
            QualifiedNameNode("off"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == "commsState"


def test_triple_with_multiple_inputs() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
                AllowedValueDecl("standby"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "deployed",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([QualifiedNameNode("deployed"), QualifiedNameNode("comms")]),
        IfNode(
            QualifiedNameNode("deployed"),
            ChooseNode(
                ListNode([QualifiedNameNode("off"), QualifiedNameNode("waiting")])
            ),
            QualifiedNameNode("off"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == "commsState"


def test_triple_with_enum_input() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
                AllowedValueDecl("standby"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "deployed",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([QualifiedNameNode("deployed"), QualifiedNameNode("off")]),
        IfNode(
            QualifiedNameNode("deployed"),
            ChooseNode(
                ListNode([QualifiedNameNode("off"), QualifiedNameNode("waiting")])
            ),
            QualifiedNameNode("off"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, TypingTripleVariableError)
    assert error.value.error.id == "off"


def test_triple_with_bad_target() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
                AllowedValueDecl("standby"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "deployed",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("off"),
        ListNode([QualifiedNameNode("deployed"), QualifiedNameNode("comms")]),
        IfNode(
            QualifiedNameNode("deployed"),
            ChooseNode(
                ListNode([QualifiedNameNode("off"), QualifiedNameNode("waiting")])
            ),
            QualifiedNameNode("off"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, TypingTripleVariableError)
    assert error.value.error.id == "off"


def test_triple_with_diff_target_and_value_types() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
                AllowedValueDecl("standby"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "deployed",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([QualifiedNameNode("deployed"), QualifiedNameNode("comms")]),
        IfNode(
            QualifiedNameNode("deployed"),
            ChooseNode(ListNode([NumberLiteralNode("4"), NumberLiteralNode("5")])),
            NumberLiteralNode("6"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, TypingAssignCompatabilityError)
    assert error.value.error.ltype == "commsState"
    assert error.value.error.rtype == BYTE


def test_triple_out_of_scope() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "commsState",
            [
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
                AllowedValueDecl("standby"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "commsState",
            [
                AllowedValueDecl("standby"),
                AllowedValueDecl("waiting"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "deployed",
            "bool",
            [AllowedValueDecl("true"), AllowedValueDecl("false")],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([QualifiedNameNode("comms")]),
        IfNode(
            QualifiedNameNode("deployed"),
            ChooseNode(
                ListNode([QualifiedNameNode("off"), QualifiedNameNode("waiting")])
            ),
            QualifiedNameNode("off"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    with pytest.raises(ErrorException) as error:
        node.accept(visitor)

    assert isinstance(error.value.error, ExpressionOutOfScope)
    assert error.value.error.id == "deployed"


def test_triple_equal_to_self() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "conditions",
            "Cond",
            [
                AllowedValueDecl("same"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "Cond",
            [
                AllowedValueDecl("same"),
                AllowedValueDecl("off"),
            ],
        )
    )
    builder.with_var_decl(
        VarDecl(
            "risk",
            "riskState",
            [AllowedValueDecl("acceptable"), AllowedValueDecl("unacceptable")],
        )
    )
    builder.with_enum_type_decl(
        EnumDecl(
            "riskState",
            [
                AllowedValueDecl("acceptable"),
                AllowedValueDecl("unacceptable"),
            ],
        )
    )
    state = builder.build().unwrap()
    node = TripleNode(
        QualifiedNameNode("conditions"),
        ListNode([QualifiedNameNode("risk"), QualifiedNameNode("conditions")]),
        IfNode(
            EqualNode(QualifiedNameNode("risk"), QualifiedNameNode("acceptable")),
            QualifiedNameNode("same"),
            QualifiedNameNode("conditions"),
        ),
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == "Cond"


def test_triple_list() -> None:
    builder = StateBuilder()
    builder.with_var_decl(
        VarDecl(
            "comms",
            "byte",
            [AllowedValueDecl("2"), AllowedValueDecl("3")],
        )
    )
    state = builder.build().unwrap()
    node = TripleListNode(
        [
            TripleNode(
                QualifiedNameNode("comms"),
                ListNode([]),
                IfNode(
                    BoolLiteralNode("true"),
                    NumberLiteralNode("2"),
                    NumberLiteralNode("3"),
                ),
            ),
            TripleNode(
                QualifiedNameNode("comms"), ListNode([]), NumberLiteralNode("3")
            ),
        ]
    )
    visitor = TypeCheckerVisitor(state)

    node.accept(visitor)
    assert len(visitor.stack) == 1
    type = visitor.stack.pop()
    assert type == "triples"
