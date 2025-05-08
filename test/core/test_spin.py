# type: ignore

from bpmncwpverify.core.spin import SpinOutput
from returns.result import Failure, Success

from returns.pipeline import is_successful
from returns.functions import not_
import pytest


@pytest.fixture
def mock_generate_counter_example(mocker):
    mock_gen_example = mocker.Mock()
    mock_gen_example.to_json.return_value = "test_json"
    mocker.patch(
        "bpmncwpverify.core.counterexample.CounterExample.generate_counterexample",
        return_value=mock_gen_example,
    )


def test_check_syntax_errors(mock_generate_counter_example):
    mock_generate_counter_example
    spin_output = SpinOutput()
    s = """
    spin: test/resources/simple_example/valid_output.pml:55, Error: syntax error    saw ''}' = 125'
    spin: test/resources/simple_example/valid_output.pml:116, Error: missing '}' ?
    """

    result = spin_output._check_syntax_errors("", s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.get_counter_example() == "test_json"
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


def test_check_syntax_errors_none(mock_generate_counter_example):
    mock_generate_counter_example
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

    result = spin_output._check_syntax_errors("", s)

    assert isinstance(result, Success)


def test_has_uncovered_states(mock_generate_counter_example):
    mock_generate_counter_example
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
        unreached in proctype otherproc
                whatever.pml:100098, state 1, "TEST1"
                whatever.pml:908, state 3, "TEST2"
                (2 of 3 states)
        unreached in init
                init.pml:100098, state 1, "INIT_TEST1"
                init.pml:908, state 3, "INIT_TEST2"
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
    spin_obj = SpinOutput()
    result = spin_obj._check_coverage_errors("", spin_output)
    assert isinstance(result, Failure)

    assert result.failure().get_counter_example() == "test_json"
    errors = result.failure().coverage_errors
    assert errors[0]["proctype"] == "testproc"
    assert errors[0]["file"] == "test.pml"
    assert errors[0]["line"] == "5"
    assert errors[0]["message"] == "\"printf('run')\""
    assert errors[1]["proctype"] == "testproc"
    assert errors[1]["file"] == "test.pml"
    assert errors[1]["line"] == "7"
    assert errors[2]["proctype"] == "otherproc"
    assert errors[2]["file"] == "whatever.pml"
    assert errors[2]["line"] == "100098"
    assert errors[2]["message"] == '"TEST1"'

    assert errors[3]["proctype"] == "otherproc"
    assert errors[3]["file"] == "whatever.pml"
    assert errors[3]["line"] == "908"
    assert errors[3]["message"] == '"TEST2"'

    assert errors[4]["proctype"] == "init"
    assert errors[4]["file"] == "init.pml"
    assert errors[4]["line"] == "100098"
    assert errors[4]["message"] == '"INIT_TEST1"'

    assert errors[5]["proctype"] == "init"
    assert errors[5]["file"] == "init.pml"
    assert errors[5]["line"] == "908"
    assert errors[5]["message"] == '"INIT_TEST2"'


def test_has_no_uncovered_states(mock_generate_counter_example):
    mock_generate_counter_example
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
    unreached in claim never_0
            test.pml:20, state 7, "-end-"
            (1 of 7 states)
    unreached in claim never_1
            test.pml:28, state 7, "-end-"
            (1 of 7 states)
    """

    spin_obj = SpinOutput()
    result = spin_obj._check_coverage_errors("", spin_output)
    assert isinstance(result, Success)


def test_check_invalid_end_state(mock_generate_counter_example):
    mock_generate_counter_example
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

    result = spin_output._check_invalid_end_state("", s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.get_counter_example() == "test_json"
    assert result.list_of_error_maps[0]["info"] == "at depth -1"


def test_check_invalid_end_state_none(mock_generate_counter_example):
    mock_generate_counter_example
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

    result = spin_output._check_invalid_end_state("", s)

    assert isinstance(result, Success)


def test_check_assertion_violation(mock_generate_counter_example):
    mock_generate_counter_example
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

    result = spin_output._check_assertion_violation("", s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.get_counter_example() == "test_json"
    assert result.list_of_error_maps[0]["assertion"] == "_nr_pr==3"


def test_check_assertion_violation_none(mock_generate_counter_example):
    mock_generate_counter_example
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

    result = spin_output._check_assertion_violation("", s)

    assert isinstance(result, Success)


def test_get_spin_output_no_errors(mock_generate_counter_example, mocker):
    mock_generate_counter_example
    file_path = "test file path"
    test_spin_output = "test spin output"
    mock_run = mocker.Mock()
    mock_run.stdout = test_spin_output
    mocker.patch("bpmncwpverify.core.spin.subprocess.run", return_value=mock_run)
    mock_stx_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_syntax_errors",
        return_value=Success(test_spin_output),
    )
    mock_invalid_end_state_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_invalid_end_state",
        return_value=Success(test_spin_output),
    )
    mock_assertion_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_assertion_violation",
        return_value=Success(test_spin_output),
    )
    mock_coverage_errors = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_coverage_errors",
        return_value=Success(test_spin_output),
    )

    result = SpinOutput.get_spin_output(file_path)
    assert is_successful(result)
    mock_stx_error.assert_called_once_with(file_path, test_spin_output)
    mock_invalid_end_state_error.assert_called_once_with(file_path, test_spin_output)
    mock_assertion_error.assert_called_once_with(file_path, test_spin_output)
    mock_coverage_errors.assert_called_once_with(file_path, test_spin_output)


def test_get_spin_output_with_errors(mock_generate_counter_example, mocker):
    mock_generate_counter_example
    test_spin_output = "test spin output"
    mock_run = mocker.Mock()
    mock_run.stdout = test_spin_output
    mocker.patch("bpmncwpverify.core.spin.subprocess.run", return_value=mock_run)
    mock_stx_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_syntax_errors",
        return_value=Failure(mocker.Mock()),
    )
    mock_invalid_end_state_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_invalid_end_state",
        return_value=Success(test_spin_output),
    )
    mock_assertion_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_assertion_violation",
        return_value=Success(test_spin_output),
    )

    result = SpinOutput.get_spin_output(test_spin_output)
    assert not_(is_successful)(result)

    mock_stx_error.assert_called_once_with("test spin output", test_spin_output)
    mock_invalid_end_state_error.assert_not_called()
    mock_assertion_error.assert_not_called()
