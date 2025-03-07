# type: ignore
from bpmncwpverify.core.spin import SpinOutput
from returns.result import Failure, Success

from returns.pipeline import is_successful
from returns.functions import not_


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


def test_get_spin_output_no_errors(mocker):
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

    result = SpinOutput.get_spin_output(test_spin_output)
    assert is_successful(result)
    mock_stx_error.assert_called_once_with(test_spin_output)
    mock_invalid_end_state_error.assert_called_once_with(test_spin_output)
    mock_assertion_error.assert_called_once_with(test_spin_output)


def test_get_spin_output_with_errors(mocker):
    test_spin_output = "test spin output"
    mock_run = mocker.Mock()
    mock_run.stdout = test_spin_output
    mocker.patch("bpmncwpverify.core.spin.subprocess.run", return_value=mock_run)
    mock_stx_error = mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_syntax_errors",
        return_value=Failure("Error"),
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
    mock_stx_error.assert_called_once_with(test_spin_output)
    mock_invalid_end_state_error.assert_not_called()
    mock_assertion_error.assert_not_called()
