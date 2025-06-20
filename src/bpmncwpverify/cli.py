import argparse
from xml.etree.ElementTree import Element

from returns.functions import not_
from returns.io import IOResult
from returns.pipeline import is_successful
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.core.accessmethods import bpmnmethods
from bpmncwpverify.core.accessmethods.cwpmethods import CwpXmlParser
from bpmncwpverify.core.error import Error, get_error_message
from bpmncwpverify.core.spin import (
    SpinVerificationReport,
    verify_with_spin,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.util.file import (
    element_tree_from_string,
    read_file_as_string,
)


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
    return argument_parser


def _verify_with_spin(
    state_str: str,
    cwp_xml: Element,
    bpmn_xml: Element,
) -> IOResult[SpinVerificationReport, Error]:
    result: IOResult[SpinVerificationReport, Error] = IOResult.from_result(
        State.from_str(state_str)
    ).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda state: IOResult.from_result(CwpXmlParser.from_xml(cwp_xml, state)).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda cwp: IOResult.from_result(
                bpmnmethods.from_xml(bpmn_xml, state)
            ).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda bpmn: verify_with_spin(state, cwp, bpmn)
            )
        )
    )

    return result


def _verify_with_spin_from_files(
    state_file: str, cwp_file: str, bpmn_file: str
) -> IOResult[SpinVerificationReport, Error]:
    result: IOResult[SpinVerificationReport, Error] = read_file_as_string(
        state_file
    ).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda state: read_file_as_string(cwp_file).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda cwp: read_file_as_string(bpmn_file).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda bpmn: web_verify(state, cwp, bpmn)
            )
        )
    )
    return result


def cli_verify(
    state_file: str, cwp_file: str, bpmn_file: str
) -> IOResult[SpinVerificationReport, Error]:
    result: IOResult[SpinVerificationReport, Error] = _verify_with_spin_from_files(
        state_file, cwp_file, bpmn_file
    )
    return result


def verify() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()

    result = cli_verify(args.state_file, args.cwp_file, args.bpmn_file)

    if not_(is_successful)(result):
        error: Error = unsafe_perform_io(result.failure())
        print(get_error_message(error))
        return

    spin_verification_report: SpinVerificationReport = unsafe_perform_io(
        result.unwrap()
    )
    print(spin_verification_report.spin_report)


def web_verify(
    state: str, cwp_str: str, bpmn_str: str
) -> IOResult[SpinVerificationReport, Error]:
    result: IOResult[SpinVerificationReport, Error] = element_tree_from_string(
        cwp_str
    ).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda cwp: element_tree_from_string(bpmn_str).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda bpmn: _verify_with_spin(state, cwp, bpmn)
        )
    )
    return result
