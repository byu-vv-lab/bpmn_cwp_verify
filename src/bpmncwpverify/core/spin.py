from typing import List

from returns.result import Failure, Result, Success
from bpmncwpverify.core.error import Error
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
from returns.pointfree import bind_result
import subprocess
import re


class SpinOutput:
    __slots__ = ["spin_msg", "error_num", "error_trace", "coverage"]

    def __init__(self, spin_msg: str) -> None:
        self.spin_msg = spin_msg
        self.error_num: Maybe[int] = Nothing
        self.error_trace: Maybe[List[Error]] = Nothing
        self.coverage: str = ""

    def _get_errors(self) -> Result["SpinOutput", "SpinOutput"]:
        error_msg = re.search(r"errors: ([0-9]+)", self.spin_msg)
        if error_msg:
            error_num = int(error_msg.group(1))
            if error_num > 0:
                self.error_num = Some(error_num)
                return Failure(self)
            else:
                return Success(self)
        else:
            assert False, "There should always be an error trace"

    def _check_syntax_errors(self) -> Result["SpinOutput", "SpinOutput"]:
        charref = re.compile(
            r"""
            (?:[\w/.:\s]*)        # Discard the 'spin: file path'
            :([0-9]+),\s        # Get the line number of syntax error
            (.*)                # Discard the Error: Syntax error
        """,
            re.VERBOSE,
        )
        iterator = charref.finditer(self.spin_msg)
        stx_errors = [error.groups() for error in iterator]
        if stx_errors:
            self.error_trace = Some(stx_errors)
            self.error_num = Some(len(stx_errors))
            return Failure(self)
        else:
            return Success(self)

    @staticmethod
    def get_spin_output(file_path: str) -> Result["SpinOutput", Error]:
        result = subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        spin_output: Result["SpinOutput", "SpinOutput"] = flow(
            SpinOutput(result),
            SpinOutput._get_errors,
            bind_result(SpinOutput._check_syntax_errors),
        )

        return spin_output
