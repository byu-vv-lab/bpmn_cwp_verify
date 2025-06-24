# type: ignore
import os
import sys

import pytest
from returns.functions import not_
from returns.pipeline import is_successful
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.cli import cli_verify, web_verify
from bpmncwpverify.core.error import Error, FileReadFileError, StateSyntaxError


def test_givin_bad_state_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = cli_verify(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, FileReadFileError)


def test_givin_bad_cwp_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = cli_verify(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, FileReadFileError)


def test_givin_bad_bpmn_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = cli_verify(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, FileReadFileError)


def test_givin_bad_state_file_when_verify_then_state_errror(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/bad_state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = cli_verify(test_args[1], test_args[2], test_args[3])

    # then
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, StateSyntaxError)


@pytest.mark.skipif(os.getenv("CI") == "true", reason="No SPIN on GitHub CI/CD")
def test_givin_good_files_when_verify_then_success(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    # when
    result = cli_verify(test_args[1], test_args[2], test_args[3])

    # then
    assert is_successful(result)
    outputs = result.unwrap()
    assert outputs is not None
    assert outputs != ""


@pytest.mark.skipif(os.getenv("CI") == "true", reason="No SPIN on GitHub CI/CD")
def test_given_good_input_when_webverify_then_success():
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


def test_given_bad_input_when_webverify_then_failure():
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
