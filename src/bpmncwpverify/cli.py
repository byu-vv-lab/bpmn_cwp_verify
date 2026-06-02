import argparse
import logging
from collections.abc import Callable
from typing import TypeVar
from xml.etree.ElementTree import Element

import requests
from returns.functions import not_
from returns.io import IOFailure, IOResult, IOSuccess
from returns.pipeline import is_successful
from returns.result import Result
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.core.accessmethods import bpmnmethods
from bpmncwpverify.core.accessmethods.cwpmethods import CwpXmlParser
from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.cbmc import (
    CbmcVerificationReport,
    verify_with_cbmc,
)
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.error import (
    Error,
    HttpError,
    JsonDecodeError,
    LambdaVerificationError,
    RequestError,
    get_error_message,
)
from bpmncwpverify.core.spin import (
    SpinVerificationReport,
    verify_with_spin,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.util.file import (
    element_tree_from_string,
    read_file_as_string,
)

LAMBDA_URL = "https://iatjgvm4gt75bw4qwbz7l3bihq0irdns.lambda-url.us-east-1.on.aws/"

logging.basicConfig(level=logging.INFO)

_R = TypeVar("_R")


def _get_argument_parser() -> "argparse.ArgumentParser":
    argument_parser = argparse.ArgumentParser(
        description="Verify the BPMN as a safe substitution for the CWP given the state"
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
    argument_parser.add_argument(
        "--cloud",
        action="store_true",
        help="Run verification remotely on AWS Lambda",
    )
    argument_parser.add_argument(
        "--cbmc",
        action="store_true",
        help="Run verification locally with CBMC",
    )
    return argument_parser


# ── Shared helpers ─────────────────────────────────────────────────────────────


def _element_tree_from_string(input: str, type: str) -> IOResult[Element, Error]:
    logging.info(f"    Converting {type} to XML tree")
    return element_tree_from_string(input)


def _verify_state(state_str: str) -> Result[State, Error]:
    logging.info("    Verifying state file")
    return State.from_str(state_str)


def _verify_cwp_with_state(cwp_xml: Element, state: State) -> IOResult[Cwp, Error]:
    logging.info("    Verifying CWP against state")
    return IOResult.from_result(CwpXmlParser.from_xml(cwp_xml, state))


def _verify_bpmn_with_state(bpmn_xml: Element, state: State) -> IOResult[Bpmn, Error]:
    logging.info("    Verifying BPMN against state")
    return IOResult.from_result(bpmnmethods.from_xml(bpmn_xml, state))


def _verify_inputs(
    state_str: str,
    cwp_xml: Element,
    bpmn_xml: Element,
    verify_fn: Callable[[State, Cwp, Bpmn], IOResult[_R, Error]],
) -> IOResult[_R, Error]:
    logging.info("Verifying state and comparing against CWP and BPMN files 0/3")
    return IOResult.from_result(_verify_state(state_str)).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda state: _verify_cwp_with_state(cwp_xml, state).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda cwp: _verify_bpmn_with_state(bpmn_xml, state).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda bpmn: verify_fn(state, cwp, bpmn)
            )
        )
    )


def _read_inputs(
    state_file: str,
    cwp_file: str,
    bpmn_file: str,
    next_fn: Callable[[str, str, str], IOResult[_R, Error]],
) -> IOResult[_R, Error]:
    logging.info("Reading input files 0/3")

    def _read(path: str) -> IOResult[str, Error]:
        logging.info(f"    Reading file: {path}")
        return read_file_as_string(path)

    return _read(state_file).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda state: _read(cwp_file).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda cwp: _read(bpmn_file).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda bpmn: next_fn(state, cwp, bpmn)
            )
        )
    )


def _print_result(result: IOResult[_R, Error], format_fn: Callable[[_R], str]) -> None:
    if not_(is_successful)(result):
        print(get_error_message(unsafe_perform_io(result.failure())))
        return
    print(format_fn(unsafe_perform_io(result.unwrap())))


# ── Verification entry points ──────────────────────────────────────────────────


def _trigger_lambda(
    state: str, cwp: str, bpmn: str
) -> IOResult[SpinVerificationReport, Error]:
    try:
        response: requests.Response = requests.post(
            url=LAMBDA_URL,
            json={
                "state": state,
                "cwp": cwp,
                "bpmn": bpmn,
            },
        )
        response.raise_for_status()
        report = response.json(object_hook=lambda obj: SpinVerificationReport(**obj))
        return IOSuccess(report)
    except requests.exceptions.HTTPError as err:
        if err.response.status_code == 400:
            return IOFailure(LambdaVerificationError(err.response.text))
        else:
            return IOFailure(
                HttpError(
                    err.response.status_code, err.response.reason, err.response.text
                )
            )
    except requests.exceptions.JSONDecodeError as err:
        return IOFailure(JsonDecodeError(err.response.text if err.response else ""))
    except requests.exceptions.RequestException as err:
        return IOFailure(RequestError(err))


def _verify_on_lambda_from_files(
    state_file: str, cwp_file: str, bpmn_file: str
) -> IOResult[SpinVerificationReport, Error]:
    return _read_inputs(state_file, cwp_file, bpmn_file, _trigger_lambda)


def _verify_with_cbmc_from_files(
    state_file: str, cwp_file: str, bpmn_file: str
) -> IOResult[CbmcVerificationReport, Error]:
    return _read_inputs(
        state_file,
        cwp_file,
        bpmn_file,
        lambda state, cwp_str, bpmn_str: _element_tree_from_string(cwp_str, "CWP").bind(  # pyright: ignore[reportUnknownMemberType]
            lambda cwp_xml: _element_tree_from_string(bpmn_str, "BPMN").bind(  # pyright: ignore[reportUnknownMemberType]
                lambda bpmn_xml: _verify_inputs(
                    state, cwp_xml, bpmn_xml, verify_with_cbmc
                )
            )
        ),
    )


# cli_verify exposes the Spin path for tests and external callers.
# May be a candidate for removal once the public API is clarified.
def cli_verify(
    state_file: str, cwp_file: str, bpmn_file: str
) -> IOResult[SpinVerificationReport, Error]:
    return _read_inputs(state_file, cwp_file, bpmn_file, web_verify)


def verify() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()

    if args.cloud and args.cbmc:
        print("ERROR: --cloud and --cbmc are mutually exclusive")
        return

    if args.cloud:
        _print_result(
            _verify_on_lambda_from_files(
                args.state_file, args.cwp_file, args.bpmn_file
            ),
            lambda r: r.spin_report,
        )
    elif args.cbmc:
        _print_result(
            _verify_with_cbmc_from_files(
                args.state_file, args.cwp_file, args.bpmn_file
            ),
            lambda r: (
                f"CBMC VERIFICATION SUCCESSFUL\n"
                f"  Workflow:    {args.bpmn_file}\n"
                f"  C file:      {r.file_path}\n"
                f"  BOUND:       {r.bound}  (--unwind {r.bound + 1})\n"
                f"  Properties:  P1-P3 passed (correctness)\n"
                f"               P4 passed ({r.reachability_output.count(': SATISFIED')} CWP states reachable)"
            ),
        )
    else:
        _print_result(
            cli_verify(args.state_file, args.cwp_file, args.bpmn_file),
            lambda r: r.spin_report,
        )


def web_verify(
    state: str, cwp_str: str, bpmn_str: str
) -> IOResult[SpinVerificationReport, Error]:
    logging.info("Converting input XML files to tree 0/2")
    return _element_tree_from_string(cwp_str, "CWP").bind(  # pyright: ignore[reportUnknownMemberType]
        lambda cwp: _element_tree_from_string(bpmn_str, "BPMN").bind(  # pyright: ignore[reportUnknownMemberType]
            lambda bpmn: _verify_inputs(state, cwp, bpmn, verify_with_spin)
        )
    )
