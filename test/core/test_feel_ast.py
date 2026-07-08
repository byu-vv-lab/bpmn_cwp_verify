from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BoolLiteralNode,
    ChooseNode,
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
    TripleNode,
    XOrNode,
)


def test_parse_number_literal() -> None:
    feel = Feel.parse("42")

    assert isinstance(feel.ast, NumberLiteralNode)
    assert feel.ast.value == "42"


def test_parse_bool_literal() -> None:
    feel = Feel.parse("true")

    assert isinstance(feel.ast, BoolLiteralNode)
    assert feel.ast.value


def test_parse_addition() -> None:
    feel = Feel.parse("1 + 2")

    assert isinstance(feel.ast, AddNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_subtraction() -> None:
    feel = Feel.parse("5 - 3")

    assert isinstance(feel.ast, SubtractNode)


def test_parse_multiplication() -> None:
    feel = Feel.parse("1 * 2")

    assert isinstance(feel.ast, MultiplyNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_power() -> None:
    feel = Feel.parse("2 ** 3")

    assert isinstance(feel.ast, PowerNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "2"
    assert feel.ast.right.value == "3"


def test_power_has_higher_precedence_than_add() -> None:
    feel = Feel.parse("2 + 3 ** 4")

    assert isinstance(feel.ast, AddNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, PowerNode)


def test_power_is_right_associative() -> None:
    feel = Feel.parse("2 ** 3 ** 4")

    assert isinstance(feel.ast, PowerNode)

    assert isinstance(feel.ast.left, PowerNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.right.value == "4"


def test_parse_less_than() -> None:
    feel = Feel.parse("1 < 2")

    assert isinstance(feel.ast, LTNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_greater_than() -> None:
    feel = Feel.parse("1 > 2")

    assert isinstance(feel.ast, GTNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_less_than_equal() -> None:
    feel = Feel.parse("1 <= 2")

    assert isinstance(feel.ast, LENode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_greater_than_equal() -> None:
    feel = Feel.parse("1 >= 2")

    assert isinstance(feel.ast, GENode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_equal() -> None:
    feel = Feel.parse("1 = 2")

    assert isinstance(feel.ast, EqualNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_not_equal() -> None:
    feel = Feel.parse("1 != 2")

    assert isinstance(feel.ast, NotEqualNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_and() -> None:
    feel = Feel.parse("1 and 2")

    assert isinstance(feel.ast, AndNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_or() -> None:
    feel = Feel.parse("1 or 2")

    assert isinstance(feel.ast, OrNode)

    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_if() -> None:
    feel = Feel.parse("if 2 then 3 else 4")

    assert isinstance(feel.ast, IfNode)

    assert isinstance(feel.ast.condition, NumberLiteralNode)
    assert isinstance(feel.ast.thendo, NumberLiteralNode)
    assert isinstance(feel.ast.elsedo, NumberLiteralNode)

    assert feel.ast.condition.value == "2"
    assert feel.ast.thendo.value == "3"
    assert feel.ast.elsedo.value == "4"


def test_parse_not() -> None:
    feel = Feel.parse("not(4)")

    assert isinstance(feel.ast, NotNode)

    assert isinstance(feel.ast.expression, NumberLiteralNode)

    assert feel.ast.expression.value == "4"


def test_parse_empty_list() -> None:
    feel = Feel.parse("[]")

    assert isinstance(feel.ast, ListNode)

    assert feel.ast.values == []


def test_parse_list() -> None:
    feel = Feel.parse("[1, 2, 3]")

    assert isinstance(feel.ast, ListNode)
    assert isinstance(feel.ast.values[0], NumberLiteralNode)
    assert isinstance(feel.ast.values[1], NumberLiteralNode)
    assert isinstance(feel.ast.values[2], NumberLiteralNode)

    assert feel.ast.values[0].value == "1"
    assert feel.ast.values[1].value == "2"
    assert feel.ast.values[2].value == "3"


def test_parse_choose() -> None:
    feel = Feel.parse("choose [1, 2, 3]")

    assert isinstance(feel.ast, ChooseNode)
    assert isinstance(feel.ast.choices, ListNode)
    assert isinstance(feel.ast.choices.values[0], NumberLiteralNode)

    assert feel.ast.choices.values[0].value == "1"


def test_parse_xor() -> None:
    feel = Feel.parse("1 Xor 2")

    assert isinstance(feel.ast, XOrNode)
    assert isinstance(feel.ast.left, NumberLiteralNode)
    assert isinstance(feel.ast.right, NumberLiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_qualified_name() -> None:
    feel = Feel.parse("x")

    assert isinstance(feel.ast, QualifiedNameNode)

    assert feel.ast.name == "x"


def test_parse_qualified_name_with_path() -> None:
    feel = Feel.parse("a.b.c")

    assert isinstance(feel.ast, QualifiedNameNode)

    assert feel.ast.name == "a.b.c"


def test_parse_triple_no_inputs() -> None:
    feel = Feel.parse("(x, [], 1)")

    assert isinstance(feel.ast, TripleNode)
    assert isinstance(feel.ast.target, QualifiedNameNode)
    assert isinstance(feel.ast.inputs, ListNode)
    assert isinstance(feel.ast.value, NumberLiteralNode)

    assert feel.ast.target.name == "x"
    assert feel.ast.inputs.values == []
    assert feel.ast.value.value == "1"


def test_parse_triple_inputs() -> None:
    feel = Feel.parse("(x, [y, z], 1)")

    assert isinstance(feel.ast, TripleNode)
    assert isinstance(feel.ast.target, QualifiedNameNode)
    assert isinstance(feel.ast.inputs, ListNode)
    assert isinstance(feel.ast.inputs.values[0], QualifiedNameNode)
    assert isinstance(feel.ast.inputs.values[1], QualifiedNameNode)
    assert isinstance(feel.ast.value, NumberLiteralNode)

    assert feel.ast.target.name == "x"
    assert feel.ast.inputs.values[0].name == "y"
    assert feel.ast.inputs.values[1].name == "z"
    assert feel.ast.value.value == "1"


def test_parse_triple_if() -> None:
    feel = Feel.parse("(x, [y, z], if y then 1 else 2)")

    assert isinstance(feel.ast, TripleNode)
    assert isinstance(feel.ast.target, QualifiedNameNode)
    assert isinstance(feel.ast.inputs, ListNode)
    assert isinstance(feel.ast.inputs.values[0], QualifiedNameNode)
    assert isinstance(feel.ast.inputs.values[1], QualifiedNameNode)
    assert isinstance(feel.ast.value, IfNode)
    assert isinstance(feel.ast.value.condition, QualifiedNameNode)
    assert isinstance(feel.ast.value.thendo, NumberLiteralNode)
    assert isinstance(feel.ast.value.elsedo, NumberLiteralNode)

    assert feel.ast.target.name == "x"
    assert feel.ast.inputs.values[0].name == "y"
    assert feel.ast.inputs.values[1].name == "z"
    assert feel.ast.value.condition.name == "y"
    assert feel.ast.value.thendo.value == "1"
    assert feel.ast.value.elsedo.value == "2"
