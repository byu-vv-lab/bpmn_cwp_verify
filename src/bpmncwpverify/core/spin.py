from returns.result import Result, Success
from bpmncwpverify.core.error import Error
import subprocess


class Coverage:
    pass


class SpinOutput:
    def _get_errors(self) -> Result[Coverage, Error]:
        return Success(Coverage())

    def _check_syntax_errors(self) -> Result[Coverage, Error]:
        return Success(Coverage())

    @staticmethod
    def get_spin_output(file_path: str) -> Result["SpinOutput", Error]:
        subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        return Success(SpinOutput())
