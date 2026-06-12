# type: ignore
import pytest
from returns.result import Failure, Success

from bpmncwpverify.core.error import TypingAssignCompatabilityError, TypingNoTypeError
from bpmncwpverify.core.feel_typechecking import (
    BOOL,
    NUMBER,
    get_type_assign,
    get_type_literal,
)


class Test_get_type_assign:
    @pytest.mark.parametrize(
        "ltype, rtype, expected_type",
        [
            ("a", "a", "a"),
            (NUMBER, NUMBER, NUMBER),
            (BOOL, BOOL, BOOL),
        ],
    )
    def test_given_good_assign_then_success(
        self, ltype: str, rtype: str, expected_type: str
    ):
        # givin
        # ltype, rtype

        # when
        result = get_type_assign(ltype, rtype)

        # then
        expected = Success(expected_type)
        assert expected == result

    @pytest.mark.parametrize(
        "ltype, rtype",
        [
            ("a", "b"),
            (BOOL, NUMBER),
            (NUMBER, BOOL),
        ],
    )
    def test_given_bad_assign_then_failure(self, ltype: str, rtype: str):
        # givin
        # ltype, rtype

        # when
        result = get_type_assign(ltype, rtype)

        # then
        expected = Failure(TypingAssignCompatabilityError(ltype, rtype))
        assert expected == result


class Test_get_type_literal:
    @pytest.mark.parametrize(
        "literal, expected_type",
        [
            ("00", NUMBER),
            ("1", NUMBER),
            ("false", BOOL),
            ("true", BOOL),
            ("2", NUMBER),
            ("255", NUMBER),
            ("256", NUMBER),
            ("-32769", NUMBER),
            ("32768", NUMBER),
            ("-2147483648", NUMBER),
            ("2147483647", NUMBER),
        ],
    )
    def test_given_good_literal_then_success(self, literal: str, expected_type: str):
        # givin
        # literal

        # when
        result = get_type_literal(literal)

        # then
        expected = Success(expected_type)
        assert expected == result

    @pytest.mark.parametrize(
        "literal",
        [
            ("False"),
            ("True"),
            ("-2147483649"),
            ("2147483648"),
        ],
    )
    def test_given_bad_literal_then_failure(self, literal: str):
        # givin
        literal = literal

        # when
        result = get_type_literal(literal)

        # then
        expected = Failure(TypingNoTypeError(literal))
        assert expected == result
