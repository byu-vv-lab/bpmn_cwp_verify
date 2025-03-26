import argparse
import builtins
from returns.pipeline import is_successful
from returns.functions import not_
from returns.io import impure_safe, IOResultE
from returns.pipeline import managed, flow
from returns.result import ResultE, Result, Success, Failure
from typing import TextIO
import requests  # type: ignore
from returns.unsafe import unsafe_perform_io

LAMBDA_URL = "https://cxvqggpd6swymxnmahwvgfsina0tiokb.lambda-url.us-east-1.on.aws/"


class Error:
    def __init__(self) -> None:
        pass


class FileError(Error):
    __slots__ = ["file_name"]

    def __init__(self, file_name: str) -> None:
        self.file_name = file_name


class HTTPError(Error):
    __slots__ = ["http_error", "http_error_text"]

    def __init__(
        self, http_error: requests.exceptions.HTTPError, http_error_text: str
    ) -> None:
        self.http_error = http_error
        self.http_error_text = http_error_text


class RequestError(Error):
    __slots__ = ["err"]

    def __init__(self, err: requests.exceptions.RequestException) -> None:
        self.err = err


def get_error_message(error: Error) -> str:
    match error:
        case FileError(file_name=file_name):
            return f"Could not get contents of {file_name} file"
        case HTTPError(http_error=http_error, http_error_text=http_error_text):
            return f"HTTP error occurred: {http_error} - Response: {http_error_text}"
        case RequestError(err=err):
            return f"Unkown error occurred while sending request: {err}"
        case _:
            raise builtins.NotImplementedError


def _get_argument_parser() -> "argparse.ArgumentParser":
    argument_parser = argparse.ArgumentParser(
        description="Verify the BPMN is a safe substitution for the CWP given the state"
    )

    argument_parser.add_argument(
        "state_file",
        help="State definition text file",
    )
    argument_parser.add_argument(
        "cwp_file",
        help="CWP state machine file in XML",
    )
    argument_parser.add_argument(
        "bpmn_file",
        help="BPMN workflow file in XML",
    )
    return argument_parser


def _get_file_contents(name: str) -> IOResultE[str]:
    return flow(
        name,
        impure_safe(lambda filename: open(filename, "r")),  # type: ignore[unused-ignore]
        managed(_read_file, _close_file),
    )


def _close_file(
    file_obj: TextIO,
    file_contents: ResultE[str],
) -> IOResultE[None]:
    return impure_safe(file_obj.close)()


def _trigger_lambda(state: str, cwp: str, bpmn: str) -> Result[str, Error]:
    try:
        response: requests.Response = requests.post(
            url=LAMBDA_URL, data={"file": [bpmn, cwp, state]}
        )
        response.raise_for_status()
        return Success(response.text)
    except requests.exceptions.HTTPError as http_err:
        return Failure(HTTPError(http_err, http_err.response.text))
    except requests.exceptions.RequestException as err:
        return Failure(RequestError(err))


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def _with_file(file_contents: IOResultE[str]) -> Result[str, str]:
    if not_(is_successful)(file_contents):
        error = unsafe_perform_io(file_contents.failure())
        return Failure(f"ERROR OCCURRED {error}")

    return Success(unsafe_perform_io(file_contents.unwrap()))


def process_command() -> Result[str, Error]:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    state_file = args.state_file

    state_str = _get_file_contents(state_file)
    if not_(is_successful)(state_str):
        return Failure(FileError(state_file))

    cwp_file = args.cwp_file
    cwp_str = _get_file_contents(cwp_file)
    if not_(is_successful)(cwp_str):
        return Failure(FileError(cwp_file))

    bpmn_file = args.bpmn_file
    bpmn_str = _get_file_contents(bpmn_file)
    if not_(is_successful)(bpmn_str):
        return Failure(FileError(bpmn_file))

    result: Result[str, Error] = _trigger_lambda(
        _with_file(state_str).unwrap(),
        _with_file(cwp_str).unwrap(),
        _with_file(bpmn_str).unwrap(),
    )
    return result
