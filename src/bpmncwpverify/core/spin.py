from returns.result import Result, Success, Failure
from typing import Dict, List
from bpmncwpverify.core.error import (
    Error,
    SpinSyntaxError,
)
import subprocess
import re


class Coverage:
    pass


class SpinOutput:
    def _get_re_matches(self, regex: str, spin_msg: str) -> List[Dict[str, str]]:
        r = re.compile(regex)

        return [
            {k: re.sub(r"\s+", " ", v).strip() for k, v in t.groupdict().items()}
            for t in r.finditer(spin_msg)
        ]

    def _check_syntax_errors(self, spin_msg: str) -> Result[Coverage, Error]:
        errors = self._get_re_matches(
            r"spin: (?P<file_path>.*?):(?P<line_number>\d+),\sError: (?P<error_msg>.*)",
            spin_msg,
        )

        return Failure(SpinSyntaxError(errors)) if errors else Success(Coverage())

    @staticmethod
    def get_spin_output(file_path: str) -> Result[Coverage, Error]:
        spin_run_string = subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        spin_output = SpinOutput()

        return spin_output._check_syntax_errors(spin_run_string)
