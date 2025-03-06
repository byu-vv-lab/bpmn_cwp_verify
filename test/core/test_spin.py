# type: ignore

from bpmncwpverify.core.spin import SpinOutput
from returns.result import Failure, Success


def test_check_syntax_errors(mocker):
    spin_output = SpinOutput()
    s = """
    spin: test/resources/simple_example/valid_output.pml:55, Error: syntax error    saw ''}' = 125'
    spin: test/resources/simple_example/valid_output.pml:116, Error: missing '}' ?
    """

    result = spin_output._check_syntax_errors(s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert (
        result.list_of_error_maps[0]["file_path"]
        == "test/resources/simple_example/valid_output.pml"
    )
    assert (
        result.list_of_error_maps[1]["file_path"]
        == "test/resources/simple_example/valid_output.pml"
    )

    assert result.list_of_error_maps[0]["line_number"] == "55"
    assert result.list_of_error_maps[1]["line_number"] == "116"

    assert result.list_of_error_maps[0]["error_msg"] == "syntax error saw ''}' = 125'"
    assert result.list_of_error_maps[1]["error_msg"] == "missing '}' ?"


def test_check_syntax_errors_none(mocker):
    spin_output = SpinOutput()
    s = """
        (Spin Version 6.5.2 -- 6 December 2019)
                + Partial Order Reduction

        Full statespace search for:
                never claim             - (none specified)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +
        ...
    """

    result = spin_output._check_syntax_errors(s)

    assert isinstance(result, Success)


def test_has_uncovered_states(mocker):
    spin_output = """

        Full statespace search for:
                never claim             + (never_0)
                assertion violations    + (if within scope of claim)
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      - (disabled by never claim)

        State-vector 20 byte, depth reached 5, errors: 0
                3 states, stored
                1 states, matched
                4 transitions (= stored+matched)
                0 atomic steps
        hash conflicts:         0 (resolved)

        Stats on memory usage (in Megabytes):
            0.000       equivalent memory usage for states (stored*(State-vector + overhead))
            0.291       actual memory usage for states
        128.000       memory used for hash table (-w24)
            0.534       memory used for DFS stack (-m10000)
        128.730       total actual memory usage


        unreached in proctype testproc
                test.pml:5, state 1, "printf('run')"
                test.pml:7, state 3, "-end-"
                (2 of 3 states)
        unreached in init
                (0 of 2 states)
        unreached in claim never_0
                test.pml:20, state 7, "-end-"
                (1 of 7 states)
        unreached in claim never_1
                test.pml:28, state 7, "-end-"
                (1 of 7 states)
    """

    result = spin_output._check_coverage_errors(spin_output)
    assert isinstance(result, Failure)


def test_has_no_uncovered_states(mocker):
    spin_output = """

        Full statespace search for:
                never claim             - (none specified)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +

        State-vector 20 byte, depth reached 6, errors: 0
                7 states, stored
                0 states, matched
                7 transitions (= stored+matched)
                0 atomic steps
        hash conflicts:         0 (resolved)

        Stats on memory usage (in Megabytes):
            0.000       equivalent memory usage for states (stored*(State-vector + overhead))
            0.292       actual memory usage for states
        128.000       memory used for hash table (-w24)
            0.534       memory used for DFS stack (-m10000)
        128.730       total actual memory usage

        unreached in proctype test
                (0 of 7 states)
        unreached in init
                (0 of 3 states)
    """

    spin_obj = SpinOutput()
    result = spin_obj._check_coverage_errors(spin_output)
    assert isinstance(result, Success)


def test_check_invalid_end_state(mocker):
    spin_output = SpinOutput()
    s = """
        pan:1: invalid end state (at depth -1)
        pan: wrote first.pml.trail

        (Spin Version 6.5.2 -- 6 December 2019)
        Warning: Search not completed
                + Partial Order Reduction

        Full statespace search for:
                never claim             - (none specified)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +
    """

    result = spin_output._check_invalid_end_state(s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.list_of_error_maps[0]["info"] == "at depth -1"


def test_check_invalid_end_state_none(mocker):
    spin_output = SpinOutput()
    s = """
        (Spin Version 6.5.2 -- 6 December 2019)
                + Partial Order Reduction

        Full statespace search for:
                never claim             - (none specified)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +
        ...
    """

    result = spin_output._check_invalid_end_state(s)

    assert isinstance(result, Success)


def test_check_assertion_violation(mocker):
    spin_output = SpinOutput()
    s = """
        pan:1: assertion violated (_nr_pr==3) (at depth 0)
        pan: wrote first.pml.trail

        (Spin Version 6.5.2 -- 6 December 2019)
        Warning: Search not completed
                + Partial Order Reduction

        Full statespace search for:
                never claim             - (not selected)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +

        State-vector 12 byte, depth reached 0, errors: 1
                1 states, stored
    """

    result = spin_output._check_assertion_violation(s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.list_of_error_maps[0]["assertion"] == "_nr_pr==3"


def test_check_assertion_violation_none(mocker):
    spin_output = SpinOutput()
    s = """
        (Spin Version 6.5.2 -- 6 December 2019)
                + Partial Order Reduction

        Full statespace search for:
                never claim             - (none specified)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +
        ...
    """

    result = spin_output._check_assertion_violation(s)

    assert isinstance(result, Success)
