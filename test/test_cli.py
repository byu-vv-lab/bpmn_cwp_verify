# type: ignore
import sys

import pytest
from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Success
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.cli import verify_result, web_verify
from bpmncwpverify.core.error import Error, MissingFileError, StateSyntaxError
from bpmncwpverify.core.state import State


@pytest.fixture
def mock_state(mocker):
    """Fixture to create a mock State object."""
    state = mocker.MagicMock()
    state._consts = []
    state._enums = []
    state._vars = []
    return state


def test_givin_bad_state_file_path_when_get_promela_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = verify_result(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, MissingFileError)
    assert error.file_name == "state.txt"


def test_givin_bad_cwp_file_path_when_get_promela_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = verify_result(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, MissingFileError)
    assert error.file_name == "test_cwp.xml"


def test_givin_bad_bpmn_file_path_when_get_promela_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = verify_result(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, MissingFileError)
    assert error.file_name == "test_bpmn.bpmn"


def test_givin_bad_state_file_when_get_promela_then_state_errror(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/bad_state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = verify_result(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, StateSyntaxError)


def test_givin_good_files_when_get_promela_then_output_promela(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = verify_result(test_args[1], test_args[2], test_args[3])

    # then
    assert is_successful(result)
    outputs = result.unwrap()
    assert outputs is not None
    assert outputs != ""


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

    # when
    result = web_verify(state, cwp, bpmn)

    # then
    assert is_successful(result)
    outputs = result.unwrap()
    assert outputs is not None
    assert outputs != ""


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
    # when
    result = web_verify(state, cwp, bpmn)

    # then
    assert not_(is_successful)(result)
    error = unsafe_perform_io(result.failure())
    assert isinstance(error, StateSyntaxError)


def test_generate_promela_with_full_state(mocker, mock_state):
    """Test generate_promela with a state containing constants, enums, and variables."""

    mock_const = mocker.MagicMock()
    mock_const.id = "MAX_COUNT"
    mock_const.init.value = "10"

    mock_enum = mocker.MagicMock()
    mock_enum.id = "TestEnum"
    mock_enum.values = [mocker.MagicMock(value="START"), mocker.MagicMock(value="STOP")]

    mock_var_enum = mocker.MagicMock()
    mock_var_enum.type_ = "int"
    mock_var_enum.id = "state_var"
    mock_var_enum.init.value = "START"

    mock_var_int = mocker.MagicMock()
    mock_var_int.type_ = "int"
    mock_var_int.id = "counter"
    mock_var_int.init.value = "0"

    mock_state._consts = [mock_const]
    mock_state._enums = [mock_enum]
    mock_state._vars = [mock_var_enum, mock_var_int]

    result = State.generate_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "#define MAX_COUNT 10\n"
        "mtype:TestEnum = {START STOP}\n"
        "int state_var = START\n"
        "int old_state_var = state_var\n"
        "int counter = 0\n"
        "int old_counter = counter\n\n"
    )

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output


def test_generate_promela_with_only_constants(mocker, mock_state):
    """Test generate_promela with only constants."""

    mock_const = mocker.MagicMock()
    mock_const.id = "BUFFER_SIZE"
    mock_const.init.value = "256"

    mock_state._consts = [mock_const]

    result = State.generate_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n#define BUFFER_SIZE 256\n\n"
    )

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output


def test_generate_promela_with_only_enums(mocker, mock_state):
    """Test generate_promela with only enums."""

    mock_enum = mocker.MagicMock()
    mock_enum.id = "TestEnum"
    mock_enum.values = [
        mocker.MagicMock(value="IDLE"),
        mocker.MagicMock(value="RUNNING"),
    ]

    mock_state._enums = [mock_enum]

    result = State.generate_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "mtype:TestEnum = {IDLE RUNNING}\n\n"
    )

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output


def test_generate_promela_with_empty_state(mock_state):
    """Test generate_promela with an empty state."""

    result = State.generate_promela(mock_state)

    expected_output = "//**********VARIABLE DECLARATION************//\n\n"

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output
