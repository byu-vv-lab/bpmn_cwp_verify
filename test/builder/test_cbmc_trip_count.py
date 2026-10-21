# type: ignore
"""
Unit tests for loop_trip_count — deriving a counter loop's real trip count.

The happy path is simple_example's shape (`x <= 5` guarding a body that does
`x + 1` from `x = 0`). Everything else must return None so the caller falls back
to max_retries; a wrong derived count is far worse than no derived count.
"""

import pytest

from bpmncwpverify.builder.cbmc_trip_count import MAX_DERIVED_TRIPS, loop_trip_count
from bpmncwpverify.core.bpmn import Task
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.state import State

# ── Helpers ────────────────────────────────────────────────────────────────────


def _state(text: str = "var x: int = 0") -> State:
    return State.from_str(text).unwrap()


def _guard(text: str) -> Feel:
    return Feel.parse(text)


def _body(*behaviors: str) -> list[Task]:
    return [Task(f"t{i}", f"t{i}", Feel.parse(b)) for i, b in enumerate(behaviors)]


# ── The shape we mean to recognise ─────────────────────────────────────────────


class TestCounterLoop:
    def test_simple_example_shape(self):
        # x = 0; body adds 1; loop while x <= 5. The acyclic pass makes x 1, then
        # the guard holds for x in 1..5 -> 5 extra trips.
        assert (
            loop_trip_count(_guard("x <= 5"), _body("(x, [x], x + 1)"), _state()) == 5
        )

    def test_strict_less_than_stops_one_earlier(self):
        assert loop_trip_count(_guard("x < 5"), _body("(x, [x], x + 1)"), _state()) == 4

    def test_step_of_two_halves_the_trips(self):
        # x goes 2, 4, 6 -> guard x <= 5 holds at 2 and 4 only.
        assert (
            loop_trip_count(_guard("x <= 5"), _body("(x, [x], x + 2)"), _state()) == 2
        )

    def test_countdown_with_subtraction(self):
        # x = 10, body subtracts 1, loop while x > 5: 9,8,7,6 hold -> 4 trips.
        assert (
            loop_trip_count(
                _guard("x > 5"), _body("(x, [x], x - 1)"), _state("var x: int = 10")
            )
            == 4
        )

    def test_mirrored_guard_is_equivalent(self):
        # `5 >= x` says the same thing as `x <= 5`.
        assert loop_trip_count(
            _guard("5 >= x"), _body("(x, [x], x + 1)"), _state()
        ) == loop_trip_count(_guard("x <= 5"), _body("(x, [x], x + 1)"), _state())

    def test_commuted_addition(self):
        assert (
            loop_trip_count(_guard("x <= 5"), _body("(x, [x], 1 + x)"), _state()) == 5
        )

    def test_guard_already_false_gives_zero_trips(self):
        assert (
            loop_trip_count(
                _guard("x <= 5"), _body("(x, [x], x + 1)"), _state("var x: int = 99")
            )
            == 0
        )

    def test_steps_from_several_tasks_accumulate(self):
        # Two tasks in the body, +1 each, so x advances by 2 per pass.
        assert (
            loop_trip_count(
                _guard("x <= 5"),
                _body("(x, [x], x + 1)", "(x, [x], x + 1)"),
                _state(),
            )
            == 2
        )


# ── Everything we must decline to guess ────────────────────────────────────────


class TestFallsBack:
    def test_no_guard(self):
        assert loop_trip_count(None, _body("(x, [x], x + 1)"), _state()) is None

    def test_no_state(self):
        assert loop_trip_count(_guard("x <= 5"), _body("(x, [x], x + 1)"), None) is None

    def test_equality_guard_is_not_a_counter(self):
        assert (
            loop_trip_count(_guard("x == 5"), _body("(x, [x], x + 1)"), _state())
            is None
        )

    def test_guard_on_a_variable_the_body_never_writes(self):
        assert (
            loop_trip_count(_guard("y <= 5"), _body("(x, [x], x + 1)"), _state())
            is None
        )

    def test_empty_body(self):
        assert loop_trip_count(_guard("x <= 5"), [], _state()) is None

    def test_body_that_does_not_move_the_variable(self):
        # Net step of zero would loop forever; decline rather than hang.
        assert (
            loop_trip_count(
                _guard("x <= 5"),
                _body("(x, [x], x + 1)", "(x, [x], x - 1)"),
                _state(),
            )
            is None
        )

    def test_non_constant_update(self):
        assert (
            loop_trip_count(_guard("x <= 5"), _body("(x, [x], x * 2)"), _state())
            is None
        )

    def test_guard_comparing_two_variables(self):
        assert (
            loop_trip_count(_guard("x <= y"), _body("(x, [x], x + 1)"), _state())
            is None
        )

    def test_variable_missing_from_state(self):
        assert (
            loop_trip_count(
                _guard("z <= 5"), _body("(z, [z], z + 1)"), _state("var x: int = 0")
            )
            is None
        )

    @pytest.mark.parametrize("limit", [MAX_DERIVED_TRIPS + 5])
    def test_absurd_trip_count_is_declined(self, limit):
        # A bound this large is unusable for CBMC anyway, so refuse to derive it.
        assert (
            loop_trip_count(_guard(f"x <= {limit}"), _body("(x, [x], x + 1)"), _state())
            is None
        )
