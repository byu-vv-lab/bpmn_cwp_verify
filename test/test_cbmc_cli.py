# type: ignore
import sys

from returns.functions import not_
from returns.io import IOSuccess
from returns.pipeline import is_successful
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.cli import _verify_with_cbmc_from_files, verify
from bpmncwpverify.core.cbmc import CbmcOutputParser, CbmcVerificationReport
from bpmncwpverify.core.error import (
    CbmcAssertionError,
    CbmcReachabilityError,
    CbmcSubProcessError,
    Error,
    FileReadFileError,
)


def _read_fixture(name: str) -> str:
    with open(f"./test/resources/cbmc/{name}") as f:
        return f.read()


# ── File-path error tests ──────────────────────────────────────────────────────


def test_bad_state_file_returns_file_read_error():
    result = _verify_with_cbmc_from_files(
        "missing_state.txt",
        "./test/resources/face2face/cwp.xml",
        "./test/resources/face2face/workflow.bpmn",
    )
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, FileReadFileError)


def test_bad_cwp_file_returns_file_read_error():
    result = _verify_with_cbmc_from_files(
        "./test/resources/face2face/state.txt",
        "missing_cwp.xml",
        "./test/resources/face2face/workflow.bpmn",
    )
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, FileReadFileError)


def test_bad_bpmn_file_returns_file_read_error():
    result = _verify_with_cbmc_from_files(
        "./test/resources/face2face/state.txt",
        "./test/resources/face2face/cwp.xml",
        "missing_workflow.bpmn",
    )
    assert not_(is_successful)(result)
    error: Error = unsafe_perform_io(result.failure())
    assert isinstance(error, FileReadFileError)


# ── Mutually exclusive flag test ───────────────────────────────────────────────


def test_cloud_and_cbmc_together_prints_error_and_returns(capsys, mocker):
    mocker.patch("bpmncwpverify.cli._verify_on_lambda_from_files")
    mocker.patch("bpmncwpverify.cli._verify_with_cbmc_from_files")
    sys.argv = [
        "verify",
        "--cloud",
        "--cbmc",
        "./test/resources/face2face/state.txt",
        "./test/resources/face2face/cwp.xml",
        "./test/resources/face2face/workflow.bpmn",
    ]
    verify()
    captured = capsys.readouterr()
    assert "mutually exclusive" in captured.out
    from bpmncwpverify.cli import (
        _verify_on_lambda_from_files,
        _verify_with_cbmc_from_files,
    )

    _verify_on_lambda_from_files.assert_not_called()
    _verify_with_cbmc_from_files.assert_not_called()


# ── Routing test ───────────────────────────────────────────────────────────────


def test_cbmc_flag_routes_to_cbmc_verifier(mocker):
    mock_cbmc = mocker.patch(
        "bpmncwpverify.cli._verify_with_cbmc_from_files",
        return_value=IOSuccess(
            CbmcVerificationReport(
                file_path="/tmp/verification.c",
                c_code="",
                bound=5,
                correctness_output=_read_fixture("correctness_success.txt"),
                reachability_output=_read_fixture("reachability_success.txt"),
            )
        ),
    )
    sys.argv = [
        "verify",
        "--cbmc",
        "./test/resources/face2face/state.txt",
        "./test/resources/face2face/cwp.xml",
        "./test/resources/face2face/workflow.bpmn",
    ]
    verify()
    mock_cbmc.assert_called_once()


# ── CbmcOutputParser unit tests ────────────────────────────────────────────────


def test_parser_correctness_success():
    parser = CbmcOutputParser()
    result = parser.check_correctness(_read_fixture("correctness_success.txt"))
    assert is_successful(result)


def test_parser_correctness_failure_returns_assertion_error():
    parser = CbmcOutputParser()
    result = parser.check_correctness(_read_fixture("correctness_failure.txt"))
    assert not is_successful(result)
    error = result.failure()
    assert isinstance(error, CbmcAssertionError)
    assert len(error.failures) > 0


def test_parser_correctness_subprocess_error_on_empty():
    parser = CbmcOutputParser()
    result = parser.check_correctness(_read_fixture("subprocess_error.txt"))
    assert not is_successful(result)
    assert isinstance(result.failure(), CbmcSubProcessError)


def test_parser_reachability_success():
    parser = CbmcOutputParser()
    result = parser.check_reachability(_read_fixture("reachability_success.txt"))
    assert is_successful(result)


def test_parser_reachability_failure_returns_reachability_error():
    parser = CbmcOutputParser()
    result = parser.check_reachability(_read_fixture("reachability_failure.txt"))
    assert not is_successful(result)
    error = result.failure()
    assert isinstance(error, CbmcReachabilityError)
    assert len(error.unsatisfied_goals) > 0


def test_parser_reachability_subprocess_error_on_empty():
    parser = CbmcOutputParser()
    result = parser.check_reachability(_read_fixture("subprocess_error.txt"))
    assert not is_successful(result)
    assert isinstance(result.failure(), CbmcSubProcessError)


# ── Integration tests (requires cbmc binary) ──────────────────────────────────


def test_face2face_with_cbmc_returns_success():
    result = _verify_with_cbmc_from_files(
        "./test/resources/face2face/state.txt",
        "./test/resources/face2face/cwp.xml",
        "./test/resources/face2face/workflow.bpmn",
    )
    assert is_successful(result)
    report = unsafe_perform_io(result.unwrap())
    assert isinstance(report, CbmcVerificationReport)
    assert report.bound > 0
