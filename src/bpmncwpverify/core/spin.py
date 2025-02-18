from returns.result import Result, Success, Failure
from bpmncwpverify.core.error import Error, SpinSyntaxError
import subprocess
import re


class Coverage:
    pass


class SpinOutput:
    def _get_errors(self, spin_msg: str) -> Result[Coverage, Error]:
        return Success(Coverage())

    def _check_syntax_errors(self, spin_msg: str) -> Result[Coverage, Error]:
        r = re.compile(
            r"""
            spin: (?P<file_path>.*?):(?P<line_number>\d+),\sError: (?P<error_msg>.*)
            """,
            re.VERBOSE,
        )

        errors = [
            {k: re.sub(r"\s+", " ", v).strip() for k, v in t.groupdict().items()}
            for t in r.finditer(spin_msg)
        ]

        return Failure(SpinSyntaxError(errors)) if errors else Success(Coverage())

    @staticmethod
    def get_spin_output(file_path: str) -> Result["SpinOutput", Error]:
        subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        return Success(SpinOutput())
