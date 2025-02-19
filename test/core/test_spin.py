from bpmncwpverify.core.spin import SpinOutput
from returns.result import Failure, Success


def test_check_syntax_errors(mocker):
    mock_spin_output = mocker.Mock()
    s = """
    spin: test/resources/simple_example/valid_output.pml:55, Error: syntax error    saw ''}' = 125'
    spin: test/resources/simple_example/valid_output.pml:116, Error: missing '}' ?
    """

    result = SpinOutput._check_syntax_errors(mock_spin_output, s)

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
    mock_spin_output = mocker.Mock()
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

    result = SpinOutput._check_syntax_errors(mock_spin_output, s)

    assert isinstance(result, Success)


def test_check_invalid_end_state(mocker):
    mock_spin_output = mocker.Mock()
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

    result = SpinOutput._check_invalid_end_state(mock_spin_output, s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.list_of_error_maps[0]["info"] == "at depth -1"


def test_check_invalid_end_state_none(mocker):
    mock_spin_output = mocker.Mock()
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

    result = SpinOutput._check_invalid_end_state(mock_spin_output, s)

    assert isinstance(result, Success)


def test_check_assertion_violation(mocker):
    mock_spin_output = mocker.Mock()
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

    result = SpinOutput._check_assertion_violation(mock_spin_output, s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert result.list_of_error_maps[0]["assertion"] == "_nr_pr==3"


def test_check_assertion_violation_none(mocker):
    mock_spin_output = mocker.Mock()
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

    result = SpinOutput._check_assertion_violation(mock_spin_output, s)

    assert isinstance(result, Success)
