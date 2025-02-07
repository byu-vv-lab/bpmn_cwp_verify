from typing import List
from bpmncwpverify.core.error import Error
from returns.maybe import Maybe
from returns.result import Failure, Result


class SpinSummary:
    pass


class SpinOutput:
    __slots__ = ["error", "coverage"]

    def __init__(self) -> None:
        self.error: Maybe[List[str]]
        self.coverage: SpinSummary


def verify_pml_with_spin(file_path: str) -> Result[SpinOutput, Error]:
    # TODO: implement
    return Failure(SpinOutput())
