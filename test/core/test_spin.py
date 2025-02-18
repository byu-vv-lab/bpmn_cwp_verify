from bpmncwpverify.core.spin import SpinOutput
from returns.result import Success, Failure
from returns.pipeline import is_successful
from returns.functions import not_


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


def test_get_spin_output(mocker):
    mock_return_val = mocker.Mock()
    mocker.patch("bpmncwpverify.core.spin.subprocess.run", return_value=mock_return_val)
    mock_return_val.stdout = "test_string"
    mocker.patch("bpmncwpverify.core.spin.SpinOutput")
    mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._get_errors",
        return_value=Success(mocker.Mock()),
    )
    mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_syntax_errors",
        return_value=Success(mocker.Mock()),
    )

    result = SpinOutput.get_spin_output("")
    assert isinstance(result, Success)
    assert is_successful(result)


def test_get_spin_output_bad_return_failure(mocker):
    mock_return_val = mocker.Mock()
    mocker.patch("bpmncwpverify.core.spin.subprocess.run", return_value=mock_return_val)
    mock_return_val.stdout = "test_string"
    mocker.patch("bpmncwpverify.core.spin.SpinOutput")
    mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._get_errors",
        return_value=Failure(mocker.Mock()),
    )
    mocker.patch(
        "bpmncwpverify.core.spin.SpinOutput._check_syntax_errors",
        return_value=Success(mocker.Mock()),
    )

    result = SpinOutput.get_spin_output("")
    assert isinstance(result, Failure)
    assert not_(is_successful)(result)
