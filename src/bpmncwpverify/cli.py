import argparse
import defusedxml.ElementTree as ElementTree

from returns.io import impure_safe, IOResultE

from returns.pipeline import managed, flow, is_successful
from returns.pointfree import bind_result
from returns.result import ResultE, Result, Success, Failure

from typing import TextIO

from bpmncwpverify.error import Error, get_error_message
from bpmncwpverify.core.state import SymbolTable
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.bpmn import Bpmn


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
    argument_parser.add_argument(
        "behavior_file",
        help="Behavior models file in Promela",
    )
    return argument_parser


def _get_file_contents(name: str) -> IOResultE[str]:
    return flow(
        name,
        impure_safe(lambda filename: open(filename, "r")),
        managed(_read_file, _close_file),
    )


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


class Builder:
    __slots__ = [
        "behavior_str",
        "bpmn",
        "bpmn_root",
        "cwp",
        "cwp_root",
        "state_str",
        "symbol_table",
    ]

    def __init__(self) -> None:
        self.behavior_str: Result[str, Error] = Failure(Error())
        self.bpmn: Result[Bpmn, Error] = Failure(Error())
        self.bpmn_root: Result[ElementTree, Error] = Failure(Error())
        self.cwp: Result[Cwp, Error] = Failure(Error())
        self.cwp_root: Result[ElementTree, Error] = Failure(Error())
        self.state_str: Result[str, Error] = Failure(Error())
        self.symbol_table: Result[SymbolTable, Error] = Failure(Error())

    def _set_symbol_table(self) -> Result["Builder", Error]:
        self.symbol_table = self.state_str.bind(SymbolTable.build)

        if is_successful(self.symbol_table):
            return Success(self)
        else:
            return Failure(self.symbol_table.failure())

    def with_behavior(self, behavior_str: str) -> "Builder":
        return self

    def with_bpmn(self, bpmn: ElementTree) -> "Builder":
        self.bpmn_root = Success(bpmn)
        return self

    def with_cwp(self, cwp: ElementTree) -> "Builder":
        self.cwp_root = Success(cwp)
        return self

    def with_state(self, state: str) -> "Builder":
        self.state_str = Success(state)
        return self

    @staticmethod
    def build_(builder: "Builder") -> Result[str, Error]:
        return builder.build()

    def build(self) -> Result[str, Error]:
        return Failure(Error())


def verify() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    state_str = _get_file_contents(args.state_file)
    bpmn_root = _get_file_contents(args.bpmn_file).map(ElementTree.fromstring)
    cwp_root = _get_file_contents(args.cwp_file).map(ElementTree.fromstring)
    behavior_str = _get_file_contents(args.behavior_file)

    builder: Builder = Builder()

    result: Result[Builder, Error | Exception] = flow(
        builder,
        (lambda i: Result.do(builder.with_state(state) for state in state_str)),
        (
            lambda i: Result.do(
                builder.with_cwp(cwp) for builder in i for cwp in cwp_root
            )
        ),
        (
            lambda i: Result.do(
                builder.with_bpmn(bpmn) for builder in i for bpmn in bpmn_root
            )
        ),
        (
            lambda i: Result.do(
                builder.with_behavior(behavior)
                for builder in i
                for behavior in behavior_str
            )
        ),
        bind_result(Builder.build_),
    )

    match result:
        case Success(_):
            pass
        case Failure(e):
            msg = get_error_message(e)
            print(msg)


def generate_stubs() -> None:
    """Generate behavior stubs for the BPMN workflow"""
    pass
