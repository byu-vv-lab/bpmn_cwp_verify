import argparse
from xml.etree.ElementTree import Element

from returns.functions import not_
from returns.io import IOFailure, IOResult, IOSuccess
from returns.pipeline import is_successful
from returns.result import Result
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.builder.promela_builder import PromelaBuilder
from bpmncwpverify.core.error import Error, get_error_message
from bpmncwpverify.core.spin import (
    SpinVerificationReport,
    SpinVerificationReportBuilder,
)
from bpmncwpverify.util.file import (
    element_tree_from_string,
    read_file_as_string,
    read_file_as_xml,
)

OUTPUT_FILE = "/tmp/verification.pml"


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


def _build_from_inputs(
    state: str,
    cwp: Element,
    bpmn: Element,
) -> IOResult[SpinVerificationReport, Error]:
    promela_result: Result[str, Error] = (
        PromelaBuilder().with_state(state).with_cwp(cwp).with_bpmn(bpmn).build()
    )

    if is_successful(promela_result):
        spin_verification_report_builder: SpinVerificationReportBuilder = (
            SpinVerificationReportBuilder()
        )
        result: IOResult[SpinVerificationReport, Error] = IOSuccess(
            promela_result.unwrap()
        ).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda promela: spin_verification_report_builder.with_file_name(OUTPUT_FILE)
            .with_promela(promela)
            .with_spin_cli_args(["-run", "-noclaim"])
            .build()
        )
        return result

    return IOFailure(promela_result.failure())


def verify_result(
    state_file: str, cwp_file: str, bpmn_file: str
) -> IOResult[SpinVerificationReport, Error]:
    result: IOResult[SpinVerificationReport, Error] = read_file_as_string(
        state_file
    ).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda state: read_file_as_xml(cwp_file).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda cwp: read_file_as_xml(bpmn_file).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda bpmn: _build_from_inputs(state, cwp, bpmn)
            )
        )
    )
    return result


def verify() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()

    result = verify_result(args.state_file, args.cwp_file, args.bpmn_file)

    if not_(is_successful)(result):
        error: Error = unsafe_perform_io(result.failure())
        print(get_error_message(error))
        return

    spin_verification_report: SpinVerificationReport = unsafe_perform_io(
        result.unwrap()
    )
    print(spin_verification_report.spin_report)


def web_verify(
    state: str, cwp: str, bpmn: str
) -> IOResult[SpinVerificationReport, Error]:
    bpmn_root = element_tree_from_string(bpmn)
    cwp_root = element_tree_from_string(cwp)
    return _build_from_inputs(state, cwp_root, bpmn_root)
