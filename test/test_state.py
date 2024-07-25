import pytest

from antlr4.error.ErrorStrategy import ParseCancellationException
from returns.pipeline import is_successful
from returns.result import Result
from returns.functions import not_

from typing import Iterable

from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.error import (
    Error,
    StateSyntaxError,
    StateMultipleDefinitionError,
)

from bpmncwpverify.state import _get_parser, _parse_state, SymbolTable
from bpmncwpverify import typechecking


@pytest.fixture(scope="module")
def bad_input() -> Iterable[str]:
    yield "enum MyEnum {a b c d} const MYCONST : foo = 10 var myenum my : MyEnum = a {b c d}"


@pytest.fixture(scope="module")
def good_input() -> Iterable[str]:
    yield "enum MyEnum {a b c d} const MYCONST : foo = 10 var myenum : MyEnum = a {b c d}"


class Test_get_parser:
    def test_given_bad_input_when_parse_state_then_ParseCancelationException(
        self, bad_input
    ):
        # given
        parser_result = _get_parser(bad_input)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        # when
        with pytest.raises(
            ParseCancellationException, match=r".* extraneous .*"
        ) as exception:
            _ = parser.state()

        # then
        assert exception.type is ParseCancellationException
        assert parser.getNumberOfSyntaxErrors() == 1
        assert (
            "line 1:58 extraneous input 'my' expecting ':'" == exception.value.args[0]
        )
        assert "line 1:58 extraneous input 'my' expecting ':'" in str(exception.value)

    def test_given_good_input_when_parse_state_then_tree_not_none(self, good_input):
        # given
        parser_result = _get_parser(good_input)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        # when
        try:
            tree = parser.state()
        except Exception as exception:
            pytest.fail("ERROR: unexpected {}".format(exception))

        # then
        assert 0 == parser.getNumberOfSyntaxErrors()
        assert tree is not None


class Test_parse_state:
    @pytest.fixture(scope="class")
    def bad_parser(self, bad_input):
        result = _get_parser(bad_input)
        yield result

    @pytest.fixture(scope="class")
    def good_parser(self, good_input):
        result = _get_parser(good_input)
        yield result

    def test_given_bad_parser_when_parse_state_then_failure(
        self, bad_parser: Result[StateParser, Error]
    ):
        # given
        assert is_successful(bad_parser), "ERROR: unexpected {}".format(str(bad_parser))

        # when
        result = bad_parser.bind(_parse_state)

        # then
        assert not is_successful(result)
        error = result.failure()
        assert isinstance(error, StateSyntaxError)
        assert "line 1:58 extraneous input 'my' expecting ':'" == error.msg

    def test_given_good_parser_when_parse_state_then_success(
        self, good_parser: Result[StateParser, Error]
    ):
        # given
        assert is_successful(good_parser), "ERROR: unexpected {}".format(
            str(good_parser)
        )

        # when
        result = good_parser.bind_result(_parse_state)

        # then
        assert is_successful(result)


# TODO:
#   * Add tests for failed enum declarations
class Test_SymbolTable_build:
    def test_given_good_input_when_build_then_success(self, good_input: str):
        # given
        # good_input

        # when
        result = SymbolTable.build(good_input)

        # then
        assert is_successful(result)

    def test_given_bad_input_when_build_then_failure(self, bad_input: str):
        # given
        # bad_input

        # when
        result = SymbolTable.build(bad_input)

        # then
        assert not_(is_successful)(result)

    @pytest.fixture(scope="class")
    def good_const_bit(self) -> Iterable[str]:
        yield "const a: bit = 0 var i : E = a {a}"

    @pytest.mark.parametrize(
        "good_input, expected",
        [
            (
                "enum E {a b} var e : E = a {a b}",
                [("E", typechecking.ENUM), ("a", "E"), ("b", "E")],
            ),
            ("enum A {b} const a: A = b var i : A = b {b}", [("a", "A")]),
            ("const a: bit = 0 var i : bit = 0 {0 1}", [("a", typechecking.BIT)]),
            (
                "const a: bool = false var i : bool = true {true false}",
                [("a", typechecking.BOOL)],
            ),
            ("const a: byte = 0 var i : byte = 0 {0 5 9}", [("a", typechecking.BYTE)]),
            (
                "const a: short = 0 var i : short = 256 {0 1 256}",
                [("a", typechecking.SHORT)],
            ),
            ("const a: int = 0 var i : int = 2", [("a", typechecking.INT)]),
            ("var i : int = 0 {0 1}", [("i", typechecking.INT)]),
        ],
    )
    def test_given_good_state_when_build_then_success(self, good_input, expected):
        # given
        # good, expected

        # when
        result = SymbolTable.build(good_input)

        # then
        assert is_successful(result)
        symbol_table: SymbolTable = result.unwrap()
        for i, expected_type in expected:
            result_type = symbol_table.get_type(i)
            assert is_successful(result_type)
            assert expected_type == result_type.unwrap()

    @pytest.mark.parametrize(
        "bad_input, expected",
        [
            (
                "enum E {e e} var i : E = a {a}",
                StateMultipleDefinitionError("e", 1, 10, 1, 8),
            ),
            (
                "enum E {e} enum E {f} var i : E = a {a}",
                StateMultipleDefinitionError("E", 1, 16, 1, 5),
            ),
            (
                "enum E {e} const e : E = 0 var i : E = a {a}",
                StateMultipleDefinitionError("e", 1, 17, 1, 8),
            ),
            (
                "const e : int = 0 var e : int = 0 {0, 1}",
                StateMultipleDefinitionError("e", 1, 22, 1, 6),
            ),
        ],
    )
    def test_given_multiple_definitions_in_state_when_build_then_failure(
        self, bad_input, expected
    ):
        # given
        # bad, expected

        # when
        result = SymbolTable.build(bad_input)

        # then
        assert not_(is_successful)(result)
        error: Error = result.failure()
        assert expected == error
