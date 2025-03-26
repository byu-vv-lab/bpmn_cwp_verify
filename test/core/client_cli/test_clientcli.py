from bpmncwpverify.client_cli.clientcli import process_command
from returns.result import Success, Failure
import sys


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

    result = process_command()
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

    result = process_command()
    assert isinstance(result, Failure)
    assert result.failure() == "Could not get contents of State file"


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

    result = process_command()
    assert isinstance(result, Failure)
    assert result.failure() == "Could not get contents of CWP file"


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

    result = process_command()
    assert isinstance(result, Failure)
    assert result.failure() == "Could not get contents of BPMN file"
