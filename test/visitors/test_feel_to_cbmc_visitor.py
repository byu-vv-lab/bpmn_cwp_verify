import pytest

from bpmncwpverify.core.error import (
    CbmcUnsupportedElementError,
    ErrorException,
)
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BoolLiteralNode,
    ChooseNode,
    DivideNode,
    EqualNode,
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
    TripleListNode,
    TripleNode,
    XOrNode,
)
from bpmncwpverify.core.state import AllowedValueDecl, State, StateBuilder, VarDecl
from bpmncwpverify.visitors.feel_to_cbmc_visitor import (
    FeelToCbmcVisitor,
    translate_feel_behavior,
    translate_feel_expr,
)


def test_list() -> None:
    node = ListNode(
        [NumberLiteralNode("2"), NumberLiteralNode("1"), NumberLiteralNode("0")]
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "{2, 1, 0}"


def test_add() -> None:
    node = AddNode(NumberLiteralNode("2"), QualifiedNameNode("3"))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(2 + 3)"


def test_multiply_and_add() -> None:
    node = AddNode(
        NumberLiteralNode("5"),
        MultiplyNode(NumberLiteralNode("2"), QualifiedNameNode("3")),
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(5 + (2 * 3))"


def test_subtract_and_divide() -> None:
    node = SubtractNode(
        DivideNode(NumberLiteralNode("4"), NumberLiteralNode("2")),
        NumberLiteralNode("1"),
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "((4 / 2) - 1)"


def test_power_node_raises() -> None:
    node = PowerNode(NumberLiteralNode("2"), NumberLiteralNode("3"))
    visitor = FeelToCbmcVisitor("")

    with pytest.raises(ErrorException):
        node.accept(visitor)


def test_and() -> None:
    node = AndNode(BoolLiteralNode("true"), QualifiedNameNode("something"))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(true && something)"


def test_or() -> None:
    node = OrNode(QualifiedNameNode("x"), QualifiedNameNode("y"))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(x || y)"


def test_xor() -> None:
    node = XOrNode(QualifiedNameNode("X"), QualifiedNameNode("Y"))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(X != Y)"


def test_or_and() -> None:
    node = OrNode(
        AndNode(QualifiedNameNode("this"), QualifiedNameNode("that")),
        XOrNode(QualifiedNameNode("this"), QualifiedNameNode("notthis")),
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "((this && that) || (this != notthis))"


@pytest.mark.parametrize(
    "node_cls,op",
    [
        (LTNode, " < "),
        (GTNode, " > "),
        (LENode, " <= "),
        (GENode, " >= "),
        (EqualNode, " == "),
        (NotEqualNode, " != "),
    ],
)
def test_comparisons(node_cls, op) -> None:
    node = node_cls(QualifiedNameNode("a"), QualifiedNameNode("b"))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == f"(a{op}b)"


def test_not() -> None:
    node = NotNode(BoolLiteralNode("true"))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "!true"


def test_true_and_not_false() -> None:
    node = AndNode(BoolLiteralNode("true"), NotNode(BoolLiteralNode("false")))
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(true && !false)"


def test_if_ternary() -> None:
    node = IfNode(
        QualifiedNameNode("blackBox"),
        QualifiedNameNode("missing"),
        QualifiedNameNode("found"),
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.expr == "(blackBox ? missing : found)"


def test_if_statement_block_raises() -> None:
    node = IfNode(
        QualifiedNameNode("cond"),
        TripleNode(QualifiedNameNode("x"), ListNode([]), NumberLiteralNode("1")),
        TripleNode(QualifiedNameNode("y"), ListNode([]), NumberLiteralNode("2")),
    )
    visitor = FeelToCbmcVisitor("task1")

    with pytest.raises(ErrorException) as excinfo:
        node.accept(visitor)

    assert isinstance(excinfo.value.error, CbmcUnsupportedElementError)


def test_choose() -> None:
    node = ChooseNode(
        ListNode([QualifiedNameNode("agreed"), QualifiedNameNode("failed")])
    )
    visitor = FeelToCbmcVisitor("Activity_1")

    node.accept(visitor)

    assert visitor.stmts == [
        "int t_choose_Activity_1_0 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_0 == agreed || t_choose_Activity_1_0 == failed);",
    ]
    assert visitor.expr == "t_choose_Activity_1_0"


def test_choose_unique_names_multiple_occurrences() -> None:
    node = TripleListNode(
        [
            TripleNode(
                QualifiedNameNode("terms"),
                ListNode([]),
                ChooseNode(
                    ListNode([QualifiedNameNode("agreed"), QualifiedNameNode("failed")])
                ),
            ),
            TripleNode(
                QualifiedNameNode("payment"),
                ListNode([]),
                ChooseNode(
                    ListNode([QualifiedNameNode("paid"), QualifiedNameNode("unpaid")])
                ),
            ),
        ]
    )
    visitor = FeelToCbmcVisitor("Activity_1")

    node.accept(visitor)

    assert visitor.stmts == [
        "int t_choose_Activity_1_0 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_0 == agreed || t_choose_Activity_1_0 == failed);",
        "terms = t_choose_Activity_1_0;",
        "int t_choose_Activity_1_1 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_1 == paid || t_choose_Activity_1_1 == unpaid);",
        "payment = t_choose_Activity_1_1;",
    ]


def test_triple() -> None:
    node = TripleNode(
        QualifiedNameNode("uuvComms"), ListNode([]), QualifiedNameNode("sent")
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.stmts == ["uuvComms = sent;"]


def test_triple_inputs_ignored() -> None:
    node = TripleNode(
        QualifiedNameNode("uuvComms"),
        ListNode([QualifiedNameNode("x")]),
        QualifiedNameNode("sent"),
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.stmts == ["uuvComms = sent;"]


def test_triple_with_choose() -> None:
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([]),
        ChooseNode(
            ListNode([QualifiedNameNode("standby"), QualifiedNameNode("waiting")])
        ),
    )
    visitor = FeelToCbmcVisitor("Activity_1")

    node.accept(visitor)

    assert visitor.stmts == [
        "int t_choose_Activity_1_0 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_0 == standby || t_choose_Activity_1_0 == waiting);",
        "comms = t_choose_Activity_1_0;",
    ]


def test_triple_with_if_ternary_value() -> None:
    node = TripleNode(
        QualifiedNameNode("blackBox"),
        ListNode([]),
        IfNode(
            EqualNode(QualifiedNameNode("uuvComms"), QualifiedNameNode("wait")),
            QualifiedNameNode("missing"),
            QualifiedNameNode("found"),
        ),
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.stmts == ["blackBox = ((uuvComms == wait) ? missing : found);"]


def test_triple_list() -> None:
    node = TripleListNode(
        [
            TripleNode(
                QualifiedNameNode("uuvComms"), ListNode([]), QualifiedNameNode("sent")
            ),
            TripleNode(QualifiedNameNode("x"), ListNode([]), QualifiedNameNode("y")),
        ]
    )
    visitor = FeelToCbmcVisitor("")

    node.accept(visitor)

    assert visitor.stmts == ["uuvComms = sent;", "x = y;"]


@pytest.mark.parametrize(
    ("interval", "lower", "upper"),
    [
        ("[1..5]", 1, 5),
        ("[1..5)", 1, 4),
        ("[1..5[", 1, 4),
        ("(1..5]", 2, 5),
        ("]1..5]", 2, 5),
        ("(1..5)", 2, 4),
        ("(1..5[", 2, 4),
        ("]1..5)", 2, 4),
        ("]1..5[", 2, 4),
        ("[1..10]", 1, 10),
        ("[5..5]", 5, 5),
        ("[0..0]", 0, 0),
        ("[0..1]", 0, 1),
        ("(0..1]", 1, 1),
        ("[1..2)", 1, 1),
        ("[255..256]", 255, 256),
        ("[32767..32768]", 32767, 32768),
        ("[32768..2147483647]", 32768, 2147483647),
        ("[2147483647..2147483647]", 2147483647, 2147483647),
    ],
)
def test_choose_interval(interval: str, lower: int, upper: int) -> None:
    feel = Feel.parse("choose " + interval)
    feel.type_check(State([], [], [], [])).unwrap()
    visitor = FeelToCbmcVisitor("Activity_1")

    feel.ast.accept(visitor)

    assert visitor.expr == "t_choose_Activity_1_0"
    assert visitor.stmts == [
        "int t_choose_Activity_1_0 = nondet_int();",
        f"__CPROVER_assume(t_choose_Activity_1_0 >= {lower} && "
        f"t_choose_Activity_1_0 <= {upper});",
    ]


def test_interval_and_list_choose_have_distinct_variables() -> None:
    feel = Feel.parse("if true then choose ]1..5) else choose [2, 4]")
    feel.type_check(State([], [], [], [])).unwrap()
    visitor = FeelToCbmcVisitor("Activity_1")

    feel.ast.accept(visitor)

    assert visitor.expr == "(true ? t_choose_Activity_1_0 : t_choose_Activity_1_1)"
    assert visitor.stmts == [
        "int t_choose_Activity_1_0 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_0 >= 2 && t_choose_Activity_1_0 <= 4);",
        "int t_choose_Activity_1_1 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_1 == 2 || t_choose_Activity_1_1 == 4);",
    ]


def test_translate_interval_behavior() -> None:
    builder = StateBuilder()
    builder.with_var_decl(VarDecl("x", "byte", [AllowedValueDecl("2")]))
    feel = Feel.parse("(x, [], choose ]1..5))")
    feel.type_check(builder.build().unwrap()).unwrap()

    lines, always_assigns = translate_feel_behavior(feel, "Activity_1")

    assert always_assigns
    assert lines == [
        "int t_choose_Activity_1_0 = nondet_int();",
        "__CPROVER_assume(t_choose_Activity_1_0 >= 2 && t_choose_Activity_1_0 <= 4);",
        "x = t_choose_Activity_1_0;",
    ]


def test_interval_choose_in_guard_requires_preamble() -> None:
    feel = Feel.parse("3 = choose [1..5]")
    feel.type_check(State([], [], [], [])).unwrap()

    with pytest.raises(ErrorException) as error:
        translate_feel_expr(feel, "flow_1")

    assert isinstance(error.value.error, CbmcUnsupportedElementError)
