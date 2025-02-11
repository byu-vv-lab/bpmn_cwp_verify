from bpmncwpverify.core.spin import SpinOutput
import pytest
from returns.maybe import Some


def test_get_errors_0_errors(mocker):
    mock_spin_output = mocker.Mock()

    s = """
        Words...
        State-vector 28 byte, depth reached 9999, errors: 0
            17750 states, stored
        Words...
    """

    SpinOutput._get_errors(mock_spin_output, s)
    assert mock_spin_output.error_num == Some(0)


def test_get_errors_15_errors(mocker):
    mock_spin_output = mocker.Mock()

    s = """
        Words...
        State-vector 28 byte, depth reached 9999, errors: 15
            17750 states, stored
        Words...
    """

    SpinOutput._get_errors(mock_spin_output, s)
    assert mock_spin_output.error_num == Some(15)


def test_get_errors_bad_input(mocker):
    mock_spin_output = mocker.Mock()

    with pytest.raises(AssertionError) as exc_info:
        SpinOutput._get_errors(mock_spin_output, "")

    assert exc_info.value.args[0] == "There should always be an error trace"


def test_check_syntax_errors(mocker):
    mock_spin_output = mocker.Mock()
    s = """
    spin: test/resources/simple_example/valid_output.pml:55, Error: syntax error    saw ''}' = 125'
    spin: test/resources/simple_example/valid_output.pml:116, Error: missing '}' ?
    """
    SpinOutput._check_syntax_errors(mock_spin_output, s)
    assert mock_spin_output.error_trace[0][0] == "55"
    assert (
        mock_spin_output.error_trace[0][1] == "Error: syntax error    saw ''}' = 125'"
    )
    assert mock_spin_output.error_trace[1][0] == "116"
    assert mock_spin_output.error_trace[1][1] == "Error: missing '}' ?"
