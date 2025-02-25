from returns.result import Result, Success, Failure
from typing import Dict, List
from bpmncwpverify.core.error import (
    Error,
    SpinSyntaxError,
    SpinInvalidEndStateError,
    SpinAssertionError,
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

    def _check_assertion_violation(self, spin_msg: str) -> Result[Coverage, Error]:
        errors = self._get_re_matches(
            r"assertion violated \((?P<assertion>.*)\) \((?P<depth>.*)\)", spin_msg
        )

        return Failure(SpinAssertionError(errors)) if errors else Success(Coverage())

    def _check_invalid_end_state(self, spin_msg: str) -> Result[Coverage, Error]:
        errors = self._get_re_matches(r"invalid end state \((?P<info>.*)\)", spin_msg)

        return (
            Failure(SpinInvalidEndStateError(errors)) if errors else Success(Coverage())
        )

    def _check_syntax_errors(self, spin_msg: str) -> Result[Coverage, Error]:
        errors = self._get_re_matches(
            r"spin: (?P<file_path>.*?):(?P<line_number>\d+),\sError: (?P<error_msg>.*)",
            spin_msg,
        )

        return Failure(SpinSyntaxError(errors)) if errors else Success(Coverage())

    def _check_coverage_errors(self, spin_msg: str) -> Result[Coverage, Error]:
        errors = self._get_re_matches(r"\((?!0)\d+ of \d+ states\)", spin_msg)

        return (
            Failure(Error(f"Coverage errors detected: {errors}"))
            if errors
            else Success(Coverage())
        )

    @staticmethod
    def get_spin_output(file_path: str) -> Result["SpinOutput", Error]:
        subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        return Success(SpinOutput())
