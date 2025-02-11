from typing import List

from returns.result import Failure, Result, Success
from bpmncwpverify.core.error import Error
from returns.maybe import Maybe, Nothing, Some
from returns.pipeline import flow
import subprocess
import re


class SpinOutput:
    __slots__ = ["spin_msg", "error_num", "error_trace", "coverage"]

    def __init__(self, spin_msg: str) -> None:
        self.spin_msg = spin_msg
        self.error_num: Maybe[int] = Nothing
        self.error_trace: Maybe[List[Error]] = Nothing
        self.coverage: str = ""

    def _get_errors(self) -> "SpinOutput":
        error_num = re.search(r"errors: ([0-9]+)", self.spin_msg)
        if error_num:
            self.error_num = Some(int(error_num.group(1)))
        else:
            assert False, "There should always be an error trace"
        return self

    def _check_syntax_errors(self) -> "SpinOutput":
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
        self.error_trace = Some(stx_errors)
        self.error_num = Some(len(stx_errors))
        return self

    @staticmethod
    def get_spin_output(file_path: str) -> Result["SpinOutput", Error]:
        try:
            result = subprocess.run(
                ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
            ).stdout

            spin_output = flow(
                SpinOutput(result),
                SpinOutput._get_errors,
                SpinOutput._check_syntax_errors,
            )
            __import__("pdb").set_trace()
            return Success(spin_output)
        except Exception as e:
            return Failure(e)
