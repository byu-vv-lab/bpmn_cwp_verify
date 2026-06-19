from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BoolLiteralNode,
    EqualNode,
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


def test_parse_number_literal() -> None:
    feel = Feel.parse("42")

    assert isinstance(feel.ast, LiteralNode)
    assert feel.ast.value == "42"


def test_parse_bool_literal() -> None:
    feel = Feel.parse("true")

    assert isinstance(feel.ast, BoolLiteralNode)
    assert feel.ast.value


def test_parse_addition() -> None:
    feel = Feel.parse("1 + 2")

    assert isinstance(feel.ast, AddNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_subtraction() -> None:
    feel = Feel.parse("5 - 3")

    assert isinstance(feel.ast, SubNode)


def test_parse_multiplication() -> None:
    feel = Feel.parse("1 * 2")

    assert isinstance(feel.ast, MultiplyNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_power() -> None:
    feel = Feel.parse("2 ** 3")

    assert isinstance(feel.ast, PowerNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "2"
    assert feel.ast.right.value == "3"


def test_power_has_higher_precedence_than_add() -> None:
    feel = Feel.parse("2 + 3 ** 4")

    assert isinstance(feel.ast, AddNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, PowerNode)


def test_power_is_right_associative() -> None:
    feel = Feel.parse("2 ** 3 ** 4")

    assert isinstance(feel.ast, PowerNode)

    assert isinstance(feel.ast.left, PowerNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.right.value == "4"


def test_parse_less_than() -> None:
    feel = Feel.parse("1 < 2")

    assert isinstance(feel.ast, LTNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_greater_than() -> None:
    feel = Feel.parse("1 > 2")

    assert isinstance(feel.ast, GTNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_less_than_equal() -> None:
    feel = Feel.parse("1 <= 2")

    assert isinstance(feel.ast, LENode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_greater_than_equal() -> None:
    feel = Feel.parse("1 >= 2")

    assert isinstance(feel.ast, GENode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_equal() -> None:
    feel = Feel.parse("1 = 2")

    assert isinstance(feel.ast, EqualNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_not_equal() -> None:
    feel = Feel.parse("1 != 2")

    assert isinstance(feel.ast, NotEqualNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_and() -> None:
    feel = Feel.parse("1 and 2")

    assert isinstance(feel.ast, AndNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_or() -> None:
    feel = Feel.parse("1 or 2")

    assert isinstance(feel.ast, OrNode)

    assert isinstance(feel.ast.left, LiteralNode)
    assert isinstance(feel.ast.right, LiteralNode)

    assert feel.ast.left.value == "1"
    assert feel.ast.right.value == "2"


def test_parse_if() -> None:
    feel = Feel.parse("if 2 then 3 else 4")

    assert isinstance(feel.ast, IfNode)

    assert isinstance(feel.ast.condition, LiteralNode)
    assert isinstance(feel.ast.thendo, LiteralNode)
    assert isinstance(feel.ast.elsedo, LiteralNode)

    assert feel.ast.condition.value == "2"
    assert feel.ast.thendo.value == "3"
    assert feel.ast.elsedo.value == "4"


def test_parse_not() -> None:
    feel = Feel.parse("not(4)")

    assert isinstance(feel.ast, NotNode)

    assert isinstance(feel.ast.expression, LiteralNode)

    assert feel.ast.expression.value == "4"
