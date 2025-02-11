from bpmncwpverify.core.spin import SpinOutput
import pytest
from returns.maybe import Some, Maybe


def test_get_errors_0_errors(mocker):
    mock_spin_output = mocker.Mock()

    s = """
        Words...
        State-vector 28 byte, depth reached 9999, errors: 0
            17750 states, stored
        Words...
    """
    mock_spin_output.spin_msg = s

    SpinOutput._get_errors(mock_spin_output)
    assert mock_spin_output.error_num == Some(0)


def test_get_errors_15_errors(mocker):
    mock_spin_output = mocker.Mock()

    s = """
        Words...
        State-vector 28 byte, depth reached 9999, errors: 15
            17750 states, stored
        Words...
    """
    mock_spin_output.spin_msg = s

    SpinOutput._get_errors(mock_spin_output)
    assert mock_spin_output.error_num == Some(15)


def test_get_errors_bad_input(mocker):
    mock_spin_output = mocker.Mock()
    mock_spin_output.spin_msg = ""

    with pytest.raises(AssertionError) as exc_info:
        SpinOutput._get_errors(mock_spin_output)

    assert exc_info.value.args[0] == "There should always be an error trace"


def test_check_syntax_errors(mocker):
    mock_spin_output = mocker.Mock()
    s = """
    spin: test/resources/simple_example/valid_output.pml:55, Error: syntax error    saw ''}' = 125'
    spin: test/resources/simple_example/valid_output.pml:116, Error: missing '}' ?
    """
    mock_spin_output.spin_msg = s
    SpinOutput._check_syntax_errors(mock_spin_output)
    match mock_spin_output.error_trace:
        case Some(x):
            assert x[0][0] == "55"
            assert x[0][1] == "Error: syntax error    saw ''}' = 125'"
            assert x[1][0] == "116"
            assert x[1][1] == "Error: missing '}' ?"
        case Maybe.empty:
            assert False


def test_get_spin_output(mocker):
    pass
