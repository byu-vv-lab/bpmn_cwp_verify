# type: ignore
from bpmncwpverify.client_cli.clientcli import (
    _verify,
    get_error_message,
    _trigger_lambda,
    _with_file,
    FileOpenError,
    Error,
    FileError,
    RequestError,
    HTTPError,
    Outputs,
    cli_verify,
)
from returns.result import Success, Failure
import sys
import pytest
from requests.exceptions import RequestException, HTTPError as httperr


def test_givin_good_state_expect_good_response(mocker):
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli._trigger_lambda",
        return_value=Success("test_success"),
    )
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    result = _verify()
    assert result.unwrap() == "test_success"


def test_givin_bad_state_expect_bad_response(mocker):
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli._trigger_lambda",
        return_value=Success("test_success"),
    )
    test_args = [
        "verify",
        "state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    result = _verify()
    assert isinstance(result, Failure)
    assert (
        get_error_message(result.failure())
        == "Could not get contents of state.txt file"
    )


def test_givin_bad_cwp_file_expect_bad_response(mocker):
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli._trigger_lambda",
        return_value=Success("test_success"),
    )
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    result = _verify()
    assert isinstance(result, Failure)
    assert (
        get_error_message(result.failure())
        == "Could not get contents of test_cwp.xml file"
    )


def test_givin_bad_bpmn_file_expect_bad_response(mocker):
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli._trigger_lambda",
        return_value=Success("test_success"),
    )
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "test_bpmn.bpmn",
    ]
    sys.argv = test_args

    result = _verify()
    assert isinstance(result, Failure)
    assert (
        get_error_message(result.failure())
        == "Could not get contents of test_bpmn.bpmn file"
    )


test_inputs: list[tuple[Error, str]] = [
    (
        FileOpenError(Exception("test")),
        "Error while getting file contents: test",
    ),
    (
        FileError("test_file_name"),
        "Could not get contents of test_file_name file",
    ),
    (
        RequestError(err=RequestException("test")),
        "Unkown error occurred while sending request: test",
    ),
    (
        HTTPError(httperr("test1"), "test2"),
        "HTTP error occurred: test1 - Response: test2",
    ),
]
test_ids: list[str] = ["FileOpenError", "FileError", "RequestError", "HTTPError"]


@pytest.mark.parametrize(
    scope="function",
    argnames=["error", "expected"],
    argvalues=test_inputs,
    ids=test_ids,
)
def test_given_error_when_get_error_message_then_message_equals_expected(
    error: Error, expected: str
):
    result = get_error_message(error)

    assert expected == result


def test_trigger_lambda_with_http_error(mocker):
    mock_response = mocker.Mock()
    mock_response.text = "test_response_text"

    mock_err = httperr("Bad request")
    mock_err.response = mock_response
    mock_response.raise_for_status.side_effect = mock_err

    mocker.patch(
        "bpmncwpverify.client_cli.clientcli.requests.post", side_effect=mock_err
    )
    return_val = _trigger_lambda(mocker.Mock(), mocker.Mock(), mocker.Mock())

    assert isinstance(return_val, Failure)
    assert isinstance(return_val.failure(), HTTPError)


def test_trigger_lambda_with_request_error(mocker):
    mock_response = mocker.Mock()

    mock_err = RequestException("Bad request")
    mock_err.response = mock_response
    mock_response.raise_for_status.side_effect = mock_err

    mocker.patch(
        "bpmncwpverify.client_cli.clientcli.requests.post", side_effect=mock_err
    )
    return_val = _trigger_lambda(mocker.Mock(), mocker.Mock(), mocker.Mock())

    assert isinstance(return_val, Failure)
    assert isinstance(return_val.failure(), RequestError)

    assert return_val.failure().err.args[0] == "Bad request"


def test_trigger_lambda_success(mocker):
    mock_response = mocker.Mock()
    mock_response.text = "test_good_response"

    mocker.patch(
        "bpmncwpverify.client_cli.clientcli.requests.post", return_value=mock_response
    )
    return_val = _trigger_lambda(mocker.Mock(), mocker.Mock(), mocker.Mock())

    returns_response = return_val.unwrap()
    assert isinstance(return_val, Success)
    assert isinstance(returns_response, Outputs)

    assert returns_response.promela == "test_good_response"


def test_cli_verify_with_verify_success(mocker):
    mock_outputs = mocker.Mock()
    mock_outputs.promela = "test_output"
    return_val = Success(mock_outputs)

    mocker.patch("bpmncwpverify.client_cli.clientcli._verify", return_value=return_val)
    mock_print = mocker.patch("builtins.print")

    cli_verify()

    mock_print.assert_called_once_with("test_output")


def test_cli_verify_with_Failure(mocker):
    mock_failure = mocker.Mock(spec=Failure)
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli._verify", return_value=mock_failure
    )
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli.get_error_message",
        return_value="test_message",
    )
    mock_print = mocker.patch("builtins.print")

    cli_verify()

    mock_print.assert_called_once_with("test_message")


def test_cli_verify_unhandeled_type(mocker):
    mocker.patch("bpmncwpverify.client_cli.clientcli._verify")

    with pytest.raises(AssertionError) as exc_info:
        cli_verify()

    assert exc_info.value.args[0] == "ERROR: unhandled type"


def test_with_file_with_failure(mocker):
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli.unsafe_perform_io", return_value="error_str"
    )
    mock_not = mocker.patch("bpmncwpverify.client_cli.clientcli.not_")
    mock_not.return_value = lambda x: True

    result = _with_file(mocker.Mock())
    assert isinstance(result, Failure)
    assert isinstance(result.failure(), FileOpenError)
    assert result.failure().err == "error_str"


def test_with_file_with_success(mocker):
    mocker.patch(
        "bpmncwpverify.client_cli.clientcli.unsafe_perform_io",
        return_value="success_str",
    )

    mock_not = mocker.patch("bpmncwpverify.client_cli.clientcli.not_")
    mock_not.return_value = lambda x: False

    result = _with_file(mocker.Mock())
    assert isinstance(result, Success)
    assert result.unwrap() == "success_str"
