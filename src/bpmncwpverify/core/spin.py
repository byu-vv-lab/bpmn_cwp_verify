from typing import List

from returns.maybe import Maybe
import subprocess


class SpinSummary:
    pass


class SpinOutput:
    __slots__ = ["error", "coverage"]

    def __init__(self) -> None:
        self.error: Maybe[List[str]]
        self.coverage: SpinSummary


def get_spin_output(file_path: str) -> str:
    result = subprocess.run(
        ["spin", "-run", "-noclaim", file_path], capture_output=True, text=True
    ).stdout
    return result
