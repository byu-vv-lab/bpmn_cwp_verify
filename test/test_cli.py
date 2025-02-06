# type: ignore
import pytest
import sys
from bpmncwpverify.core.state import State
from returns.pipeline import is_successful
from returns.functions import not_
from returns.result import Success

from bpmncwpverify.cli import _verify, web_verify
from bpmncwpverify.core.error import MissingFileError, StateSyntaxError


@pytest.fixture
def mock_state(mocker):
    """Fixture to create a mock State object."""
    state = mocker.MagicMock()
    state._consts = []
    state._enums = []
    state._vars = []
    return state


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


def test_generate_promela_with_full_state(mocker, mock_state):
    """Test generate_promela with a state containing constants, enums, and variables."""

    mock_const = mocker.MagicMock()
    mock_const.id = "MAX_COUNT"
    mock_const.init.value = "10"

    mock_enum = mocker.MagicMock()
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
        "mtype = {START STOP}\n"
        "int state_var = START\n"
        "int counter = 0"
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
        "//**********VARIABLE DECLARATION************//\n" "#define BUFFER_SIZE 256"
    )

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output


def test_generate_promela_with_only_enums(mocker, mock_state):
    """Test generate_promela with only enums."""

    mock_enum = mocker.MagicMock()
    mock_enum.values = [
        mocker.MagicMock(value="IDLE"),
        mocker.MagicMock(value="RUNNING"),
    ]

    mock_state._enums = [mock_enum]

    result = State.generate_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n" "mtype = {IDLE RUNNING}"
    )

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output


def test_generate_promela_with_empty_state(mock_state):
    """Test generate_promela with an empty state."""

    result = State.generate_promela(mock_state)

    expected_output = "//**********VARIABLE DECLARATION************//"

    assert isinstance(result, Success)
    assert result.unwrap() == expected_output
