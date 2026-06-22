# type: ignore
from collections.abc import Iterable

import pytest
from antlr4.error.ErrorStrategy import ParseCancellationException
from returns.pipeline import is_successful

from bpmncwpverify.core.feel import Feel


@pytest.fixture(scope="module")
def parenthesis_input() -> Iterable[str]:
    yield "(1 + 1)"


@pytest.fixture(scope="module")
def id_input() -> Iterable[str]:
    yield "a"


@pytest.fixture(scope="module")
def negator_input() -> Iterable[str]:
    yield "-1"


@pytest.fixture(scope="module")
def mult_input() -> Iterable[str]:
    yield "1 * 1"


@pytest.fixture(scope="module")
def div_input() -> Iterable[str]:
    yield "1/1"


@pytest.fixture(scope="module")
def addition_input() -> Iterable[str]:
    yield "1 + 1"


@pytest.fixture(scope="module")
def subtraction_input() -> Iterable[str]:
    yield "1 - 1"


@pytest.fixture(scope="module")
def rel_input() -> Iterable[str]:
    yield "1 = 1"


@pytest.fixture(scope="module")
def not_input() -> Iterable[str]:
    yield "not(true)"


@pytest.fixture(scope="module")
def and_input() -> Iterable[str]:
    yield "1 and 1"


@pytest.fixture(scope="module")
def or_input() -> Iterable[str]:
    yield "1 or 1"


@pytest.fixture(scope="module")
def bad_input_unaryInBinary() -> Iterable[str]:
    yield "1 +++ 10"


@pytest.fixture(scope="module")
def bad_input_badOperator() -> Iterable[str]:
    yield "a = * 10"


@pytest.fixture(scope="module")
def bad_input_binaryInUnary() -> Iterable[str]:
    yield "* 1"


class Test_bad_inputs:
    def test_bad_Unaryinput(self, bad_input_unaryInBinary):
        parser_result = Feel().parse(bad_input_unaryInBinary)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        with pytest.raises(
            ParseCancellationException, match=r".* extraneous .*"
        ) as exception:
            _ = parser.compilation_unit()

        assert exception.type is ParseCancellationException
        assert parser.getNumberOfSyntaxErrors() == 1

    def test_bad_Binaryinput(self, bad_input_binaryInUnary):
        parser_result = Feel().parse(bad_input_binaryInUnary)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        with pytest.raises(
            ParseCancellationException, match=r".* extraneous .*"
        ) as exception:
            _ = parser.compilation_unit()

        assert exception.type is ParseCancellationException
        assert parser.getNumberOfSyntaxErrors() == 1

    def test_bad_Operatorinput(self, bad_input_badOperator):
        parser_result = Feel().parse(bad_input_badOperator)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        with pytest.raises(
            ParseCancellationException, match=r".* extraneous .*"
        ) as exception:
            _ = parser.compilation_unit()

        assert exception.type is ParseCancellationException
        assert parser.getNumberOfSyntaxErrors() == 1


def test_parenthesis_input_test(parenthesis_input):
    parser_result = Feel().parse(parenthesis_input)
    parser = parser_result.unwrap()
    tree = parser.compilation_unit()
    assert tree is not None


def test_id_input_test(id_input):
    parser_result = Feel().parse(id_input)
    parser = parser_result.unwrap()
    tree = parser.compilation_unit()
    assert tree is not None


def test_negator_input_test(negator_input):
    parser_result = Feel().parse(negator_input)
    parser = parser_result.unwrap()
    # tree = parser.start()
    # print("Parse Tree Structure:", tree.toStringTree(recog=parser))
    id = parser.compilation_unit()
    assert id is not None


def test_mult_input_test(mult_input):
    parser_result = Feel().parse(mult_input)
    parser = parser_result.unwrap()
    id = parser.multiplicativeExpression()
    assert id is not None


def test_div_input_test(div_input):
    parser_result = Feel().parse(div_input)
    parser = parser_result.unwrap()
    id = parser.multiplicativeExpression()
    assert id is not None


def test_add_input_test(addition_input):
    parser_result = Feel().parse(addition_input)
    parser = parser_result.unwrap()
    id = parser.compilation_unit()
    assert id is not None


def test_subtract_input_test(subtraction_input):
    parser_result = Feel().parse(subtraction_input)
    parser = parser_result.unwrap()
    id = parser.additiveExpression()
    assert id is not None


def test_rel_input_test(rel_input):
    parser_result = Feel().parse(rel_input)
    parser = parser_result.unwrap()
    id = parser.compilation_unit()
    assert id is not None


def test_not_input_test(not_input):
    parser_result = Feel().parse(not_input)
    parser = parser_result.unwrap()
    id = parser.compilation_unit()
    assert id is not None


def test_and_input_test(and_input):
    parser_result = Feel().parse(and_input)
    parser = parser_result.unwrap()
    id = parser.conditionalAndExpression()
    assert id is not None


def test_or_input_test(or_input):
    parser_result = Feel().parse(or_input)
    parser = parser_result.unwrap()
    id = parser.conditionalOrExpression()
    assert id is not None


@pytest.mark.parametrize(
    "input_text",
    [
        "a",
        "(a)",
        "a + b",
        "a * b",
        "-a",
        # Unary and Binary Operations
        "-a + b",
        "a + b * c",
        "a * b + c",
        "(a + b) * c",
        "-a * -b",
        # Logical and Relational Operations
        "a < b",
        "a <= b",
        "a = b",
        "a > b",
        "a >= b",
        "not(a)",
        "not(a and b)",
        "a and b",
        "a or b",
        "a and b or c",
        "(a or b) and c",
        "a < b and c > d",
        "a + b = c - d",
        "(a < b) and (c >= d)",
        # Complex Nested Expressions
        "a * (b + c) / d",
        "a + b * (c - d) / e",
        "-a + (b * c) / (-d + e)",
        "a and (b or not(c))",
        "not(a < b) and (c > d)",
        "a < b + c * d",
        "(a + b) <= (c - d * e)",
        "not(a = b) or not(c = d)",
        "a + b * c = d / e - f",
        "not(a) or not(b) and not(c)",
        "a < b or (c >= d and e < f)",
        # Complex Combinations
        "((a + b) * c < d) and e",
        "(a / b) * (c + d) - e",
        "a and b or c and d",
        "(a < b or c > d) and (e >= f or g <= h)",
        "(a < b or c > d) and e >= f or g <= h",
        "((a < b or c > d) and e >= f or g <= h) > (a - b - (c - d - g * h))",
        "a + (b * (c - d / e)) >= f",
        "((a and b) or not(c)) and d",
        # Edge Cases with Nested Parentheses and Unary Operators
        "((((a))))",
        "-(a + b * c)",
        "not(not(a and b))",
        "((((a + b)) * (c - d)))",
        "a * -(b + c)",
        "not((a + b) * (c - d) / e)",
        "((a and b) or (c and d))",
        "not(not(nota))",
        "((a or b) and (not(c) or d))",
    ],
)
def test_valid_inputs(input_text):
    parser_res = Feel().parse(input_text)
    parser = parser_res.unwrap()

    tree = parser.compilation_unit()

    assert tree is not None
    assert parser.getNumberOfSyntaxErrors() == 0


@pytest.mark.parametrize(
    "input_text",
    [
        "and b",
        "(a + b",
        "a + (b * c",
        "(a and b))",
        "a + (b * (c - d)",
        "((a + b) * c < d and e",
        "a * (b + c))",
        "a or (b and c",
        "(a or b ad",
        "(a + b))",
        "a and (b or c",
        "((a + b)",
        "+",
        "*",
        "and",
        "or",
        "(",
        ")",
        "not((a and b) or)",
        "(a or b)) * c",
    ],
)
def test_invalid_inputs(input_text):
    with pytest.raises(ParseCancellationException):
        parser_res = Feel().parse(input_text)
        parser = parser_res.unwrap()
        tree = parser.compilation_unit()
        tree.toStringTree(recog=parser)
