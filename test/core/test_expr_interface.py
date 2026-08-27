# type: ignore
import pytest
from returns.pipeline import is_successful

from bpmncwpverify.core.error import (
    ExpressionComputationCompatabilityError,
    ExpressionNegatorError,
    ExpressionRelationalNotError,
    ExpressionRelationCompatabilityError,
    ExpressionUnrecognizedID,
)
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.state import State


@pytest.mark.parametrize(
    "state, expression, expression_type",
    [
        ("var a: bit var b: bit ", "a != b", "bool"),
        ("const x: int = 0 var y: short var z: short", "x + y - z", "int"),
        ("var a: int var b: byte", "a > b", "bool"),
        ("const x: bool = true var y: bool", "!x || y", "bool"),
        (
            "var m: int var n: short var o: bool",
            "(m >= n) && !o",
            "bool",
        ),
        (
            "var p: int var q: short var r: byte",
            "(p + q) * r == p",
            "bool",
        ),
        ("var a: byte var b: bit", "(a != b) || (a > b)", "bool"),
        (
            "const x: int = 4 var y: short var z: byte",
            "x * (y + z) < x",
            "bool",
        ),
        ("var i: int var j: short var k: bit", "(i + j) > k", "bool"),
        ("var a: int var b: short var c: bool", "(a > b) && !c", "bool"),
        ("const a: bit = 0 var b: short", "b + a", "short"),
        ("const x: int = 0 var y: short var z: bit", "x + y - z", "int"),
        ("const a: bit = 0 var b: short var c: int", "a + (b * c)", "int"),
        # (
        #     "array a[2]: int = {1 2} array b[2]: int = {3 4} var x: int = 0",
        #     "a[0] + b[1]",
        #     "int",
        # ),
        # (
        #     "array a[2]: int = {1 2} array b[2]: int = {3 4} var x: int = 0",
        #     "a[0] != b[1]",
        #     "bool",
        # ),
    ],
)
def test_given_good_state_when_build_then_success(state, expression, expression_type):
    sym_table_result = State.from_str(state)

    assert is_successful(sym_table_result)
    state: State = sym_table_result.unwrap()

    expr_checker_result = ExpressionListener.type_check(expression, state)

    assert is_successful(expr_checker_result)

    assert expr_checker_result.unwrap() == expression_type


@pytest.mark.parametrize(
    "state, expression, error",
    [
        ("const a: bit = 0 var b: short", "b + c", ExpressionUnrecognizedID),
        (
            "const a: short = 0 var b: short var c: short",
            "a + (b > c)",
            ExpressionComputationCompatabilityError,
        ),
        ("var a: bit", "!a", ExpressionRelationalNotError),
        (
            "var a: bool var b: bool",
            "a + b",
            ExpressionComputationCompatabilityError,
        ),
        ("var a: bool", "-a", ExpressionNegatorError),
        (
            "var a: int var b: bool",
            "a < b",
            ExpressionRelationCompatabilityError,
        ),
    ],
)
def test_given_bad_state_when_build_then_failure(state, expression, error):
    sym_table_result = State.from_str(state)

    assert is_successful(sym_table_result)
    state: State = sym_table_result.unwrap()

    expr_checker_result = ExpressionListener.type_check(expression, state)

    assert not is_successful(expr_checker_result)

    res_error = expr_checker_result.failure()

    assert isinstance(res_error, error)
