import argparse
from returns.pipeline import is_successful
from returns.functions import not_
from returns.io import impure_safe, IOResultE
from returns.pipeline import managed, flow
from returns.result import ResultE
from typing import TextIO

LAMBDA_URL = "https://cxvqggpd6swymxnmahwvgfsina0tiokb.lambda-url.us-east-1.on.aws/"


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
    argument_parser.add_argument(
        "behavior_file",
        help="Behavior models file in Promela",
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


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def process_command() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    state_file = args.state_file
    state_str = _get_file_contents(state_file)
    if not_(is_successful)(state_str):
        pass
    bpmn_file = args.bpmn_file
    bpmn_str = _get_file_contents(bpmn_file)
    if not_(is_successful)(bpmn_str):
        pass
    cwp_file = args.cwp_file
    cwp_root: IOResultE[str] = _get_file_contents(cwp_file)
    if not_(is_successful)(cwp_root):
        pass
    behavior_file = args.behavior_file
    behavior_str = _get_file_contents(behavior_file)
    if not_(is_successful)(behavior_str):
        pass


if __name__ == "__main__":
    process_command()
