from bpmncwpverify.core.spin import SpinOutput
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
