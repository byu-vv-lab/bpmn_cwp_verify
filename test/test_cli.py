# type: ignore
import sys
from returns.pipeline import is_successful
from returns.functions import not_

from bpmncwpverify.cli import _verify, web_verify
from bpmncwpverify.core.error import MissingFileError, StateSyntaxError


def test_givin_bad_state_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
        "./test/resources/simple_example/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    assert isinstance(result.failure(), MissingFileError)
    assert result.failure().file_name == "state.txt"


def test_givin_bad_cwp_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
        "./test/resources/simple_example/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    assert isinstance(result.failure(), MissingFileError)
    assert result.failure().file_name == "test_cwp.xml"


def test_givin_bad_bpmn_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "test_bpmn.bpmn",
        "./test/resources/simple_example/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    assert isinstance(result.failure(), MissingFileError)
    assert result.failure().file_name == "test_bpmn.bpmn"


def test_givin_bad_behavior_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
        "behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    assert isinstance(result.failure(), MissingFileError)
    assert result.failure().file_name == "behavior.txt"


def test_givin_bad_state_file_when_verify_then_state_errror(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/bad_state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
        "./test/resources/simple_example/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, StateSyntaxError)


def test_givin_good_files_when_verify_then_output_promela(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
        "./test/resources/simple_example/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert is_successful(result)
    outputs = result.unwrap()
    assert outputs.promela is not None
    assert outputs.promela != ""


def test_good_input_webverify_output_promela():
    # given
    bpmn = ""
    with open("./test/resources/simple_example/test_bpmn.bpmn", "r") as bpmn_file:
        for line in bpmn_file:
            bpmn += line

    cwp = ""
    with open("./test/resources/simple_example/test_cwp.xml", "r") as cwp_file:
        for line in cwp_file:
            cwp += line

    state = ""
    with open("./test/resources/simple_example/state.txt", "r") as state_file:
        for line in state_file:
            state += line

    behavior = ""
    with open("./test/resources/simple_example/behavior.txt", "r") as behavior_file:
        for line in behavior_file:
            behavior += line
    # when
    result = web_verify(bpmn, cwp, state, behavior)

    # then
    assert is_successful(result)
    outputs = result.unwrap()
    assert outputs.promela is not None
    assert outputs.promela != ""


def test_bad_input_webverify_output_error():
    # given
    bpmn = ""
    with open("./test/resources/simple_example/test_bpmn.bpmn", "r") as bpmn_file:
        for line in bpmn_file:
            bpmn += line

    cwp = ""
    with open("./test/resources/simple_example/test_cwp.xml", "r") as cwp_file:
        for line in cwp_file:
            cwp += line

    state = ""
    with open("./test/resources/simple_example/bad_state.txt", "r") as state_file:
        for line in state_file:
            state += line

    behavior = ""
    with open("./test/resources/simple_example/behavior.txt", "r") as behavior_file:
        for line in behavior_file:
            behavior += line
    # when
    result = web_verify(bpmn, cwp, state, behavior)

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, StateSyntaxError)
