from typing import List

from bpmncwpverify.core.error import Error
from returns.maybe import Maybe, Nothing, Some
import subprocess
import re


class SpinSummary:
    pass


class SpinOutput:
    __slots__ = ["error_num", "error_trace", "coverage"]

    def __init__(self) -> None:
        self.error_num: Maybe[int] = Nothing
        self.error_trace: Maybe[List[Error]] = Nothing
        self.coverage: SpinSummary = SpinSummary()

    def _get_errors(self, s: str) -> "SpinOutput":
        error_num = re.search(r"errors: ([0-9]+)", s)
        if error_num:
            self.error_num = Some(int(error_num.group(1)))
        else:
            assert False, "There should always be an error trace"

        return self

    def _check_syntax_errors(self, s: str) -> "SpinOutput":
        charref = re.compile(
            r"""
            (?:[\w/.:\s]*)        # Discard the 'spin: file path'
            :([0-9]+),\s        # Get the line number of syntax error
            (.*)                # Discard the Error: Syntax error
        """,
            re.VERBOSE,
        )
        iterator = charref.finditer(s)
        self.error_trace = Some([error.groups() for error in iterator])
        return self

    @staticmethod
    def get_spin_output(file_path: str) -> "SpinOutput":
        spin_output = SpinOutput()
        result = subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        return spin_output._get_errors(result)
