from returns.result import Result, Success
from bpmncwpverify.core.error import Error
import subprocess


class Coverage:
    pass


class SpinOutput:
    @staticmethod
    def get_spin_output(file_path: str) -> Result[Coverage, Error]:
        subprocess.run(
            ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
        ).stdout

        return Success(Coverage())
