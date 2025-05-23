import argparse
from defusedxml import ElementTree
from xml.etree.ElementTree import Element

from bpmncwpverify.builder.filebuilder import StateBuilder, Outputs
from returns.io import impure_safe, IOResult, IOResultE
from returns.curry import partial
from returns.pipeline import managed, flow
from returns.pointfree import bind_result
from returns.result import ResultE, Result, Success, Failure
from returns.pipeline import is_successful
from returns.functions import not_

from typing import TextIO, cast

from bpmncwpverify.core.error import Error, MissingFileError, get_error_message
from bpmncwpverify.core.spin import SpinOutput, CoverageReport

OUTPUT_FILE = "/tmp/verification.pml"


def element_tree_from_string(input: str) -> Element:
    return cast(Element, ElementTree.fromstring(input))  # type: ignore[unused-ignore]


def _close_file(
    file_obj: TextIO,
    file_contents: ResultE[str],
) -> IOResultE[None]:
    return impure_safe(file_obj.close)()


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


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def _verify() -> Result["Outputs", Error]:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    state_file = args.state_file
    state_str = _get_file_contents(state_file)
    if not_(is_successful)(state_str):
        return Failure(MissingFileError(state_file))
    bpmn_file = args.bpmn_file
    bpmn_root: IOResultE[Element] = _get_file_contents(bpmn_file).map(
        element_tree_from_string
    )
    if not_(is_successful)(bpmn_root):
        return Failure(MissingFileError(bpmn_file))
    cwp_file = args.cwp_file
    cwp_root: IOResultE[Element] = _get_file_contents(cwp_file).map(
        element_tree_from_string
    )
    if not_(is_successful)(cwp_root):
        return Failure(MissingFileError(cwp_file))

    builder: StateBuilder = StateBuilder()

    result: Result["Outputs", Error] = flow(
        Success(builder),
        partial(StateBuilder.with_state_, state_str),
        partial(StateBuilder.with_cwp_, cwp_root),
        partial(StateBuilder.with_bpmn_, bpmn_root),
        bind_result(StateBuilder.build_),
    )

    return result


# add a flag to get promela
# 1) call promela_generation > file.pml
# 2) call get_spin_output
# 3) put file in /tmp
# 4) returns either counter example or coverage report
# use error interface instead of .get_counter_example()


def verify() -> None:
    result: Result[Outputs, Error] = _verify()

    match result:
        case Success(o):
            with open(OUTPUT_FILE, "w") as f:
                f.write(o.promela)
            spin_output: Result[CoverageReport, str] = SpinOutput.get_spin_output(
                OUTPUT_FILE
            )
            if not_(is_successful)(spin_output):
                print(spin_output.failure())
            else:
                print(spin_output.unwrap().full_spin_output)
        case Failure(e):
            msg = get_error_message(e)
            print(msg)
        case _:
            assert False, "ERROR: unhandled type"


def web_verify(bpmn: str, cwp: str, state: str) -> Result["Outputs", Error]:
    bpmn_root: IOResultE[Element] = IOResult.from_value(element_tree_from_string(bpmn))
    cwp_root: IOResultE[Element] = IOResult.from_value(element_tree_from_string(cwp))

    builder: StateBuilder = StateBuilder()

    result: Result["Outputs", Error] = flow(
        Success(builder),
        partial(StateBuilder.with_state_, IOResult.from_value(state)),
        partial(StateBuilder.with_cwp_, cwp_root),
        partial(StateBuilder.with_bpmn_, bpmn_root),
        bind_result(StateBuilder.build_),
    )

    return result
