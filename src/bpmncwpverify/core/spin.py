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
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result


class Coverage:
    pass


class SpinOutput:
    def _get_re_matches(self, regex: str, spin_msg: str) -> List[Dict[str, str]]:
        r = re.compile(regex)

        return [
            {k: re.sub(r"\s+", " ", v).strip() for k, v in t.groupdict().items()}
            for t in r.finditer(spin_msg)
        ]

    def _check_invalid_end_state(self, spin_msg: str) -> Result[str, Error]:
        errors = self._get_re_matches(r"invalid end state \((?P<info>.*)\)", spin_msg)

        return (
            Failure(SpinInvalidEndStateError(errors)) if errors else Success(spin_msg)
        )

    def _check_assertion_violation(self, spin_msg: str) -> Result[str, Error]:
        errors = self._get_re_matches(
            r"assertion violated \((?P<assertion>.*)\) \((?P<depth>.*)\)", spin_msg
        )

        return Failure(SpinAssertionError(errors)) if errors else Success(spin_msg)

    def _check_syntax_errors(self, spin_msg: str) -> Result[str, Error]:
        errors = self._get_re_matches(
            r"spin: (?P<file_path>.*?):(?P<line_number>\d+),\sError: (?P<error_msg>.*)",
            spin_msg,
        )

        return Failure(SpinSyntaxError(errors)) if errors else Success(spin_msg)

    @staticmethod
    def get_spin_output(file_path: str) -> Result[Coverage, Error]:
        spin_run_string = subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        spin_output = SpinOutput()

        result: Result[str, Error] = flow(
            spin_run_string,
            spin_output._check_syntax_errors,
            bind_result(spin_output._check_invalid_end_state),
            bind_result(spin_output._check_assertion_violation),
        )
        if is_successful(result):
            return Success(Coverage())
        return Failure(result.failure())
