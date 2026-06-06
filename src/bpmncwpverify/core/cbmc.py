import re
import subprocess

from returns.io import IOResult, IOSuccess, impure_safe
from returns.result import Failure, Result, Success

from bpmncwpverify.builder.cbmc_builder import CbmcBuilder
from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.error import (
    CbmcAssertionError,
    CbmcReachabilityError,
    CbmcSubProcessError,
    Error,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.util.file import write_file_contents

OUTPUT_FILE = "./tmp/verification.c"


class CbmcVerificationReport:
    __slots__ = [
        "file_path",
        "c_code",
        "bound",
        "correctness_output",
        "reachability_output",
    ]

    def __init__(
        self,
        file_path: str,
        c_code: str,
        bound: int,
        correctness_output: str,
        reachability_output: str,
    ) -> None:
        self.file_path = file_path
        self.c_code = c_code
        self.bound = bound
        self.correctness_output = correctness_output
        self.reachability_output = reachability_output


class CbmcOutputParser:
    def check_correctness(self, stdout: str) -> Result[None, Error]:
        if "VERIFICATION SUCCESSFUL" in stdout:
            return Success(None)
        if "VERIFICATION FAILED" in stdout:
            failures = re.findall(r"^\[.*?\].*?: FAILURE$", stdout, re.MULTILINE)
            return Failure(CbmcAssertionError(failures))
        return Failure(CbmcSubProcessError("cbmc"))

    def check_reachability(self, stdout: str) -> Result[None, Error]:
        goal_lines = re.findall(
            r"^\[main\.coverage\.\d+\].*?: (SATISFIED|FAILED)$", stdout, re.MULTILINE
        )
        if not goal_lines:
            return Failure(CbmcSubProcessError("cbmc --cover"))
        unsatisfied = [
            line
            for line in re.findall(r"^\[main\.coverage\.\d+\].*$", stdout, re.MULTILINE)
            if line.endswith("FAILED")
        ]
        if unsatisfied:
            return Failure(CbmcReachabilityError(unsatisfied))
        return Success(None)


def _run_cbmc(args: list[str]) -> IOResult[str, Error]:
    cmd = args[0]

    def _subprocess() -> str:
        result = subprocess.run(args, capture_output=True, text=True)
        return result.stdout + result.stderr

    return impure_safe(_subprocess)().alt(lambda _: CbmcSubProcessError(cmd))


def verify_with_cbmc(
    state: State,
    cwp: Cwp,
    bpmn: Bpmn,
) -> IOResult[CbmcVerificationReport, Error]:
    builder = CbmcBuilder().with_state(state).with_cwp(cwp).with_bpmn(bpmn)
    build_result = builder.build()
    bound = builder.last_bound

    parser = CbmcOutputParser()
    unwind = str(bound + 1)

    result: IOResult[CbmcVerificationReport, Error] = IOResult.from_result(
        build_result
    ).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda c_code: write_file_contents(c_code, OUTPUT_FILE).bind(  # pyright: ignore[reportUnknownMemberType]
            lambda _: _run_cbmc(["cbmc", OUTPUT_FILE, "--unwind", unwind]).bind(  # pyright: ignore[reportUnknownMemberType]
                lambda correctness_out: IOResult.from_result(
                    parser.check_correctness(correctness_out)
                ).bind(  # pyright: ignore[reportUnknownMemberType]
                    lambda _: _run_cbmc(
                        [
                            "cbmc",
                            OUTPUT_FILE,
                            "--unwind",
                            unwind,
                            "--cover",
                            "cover",
                            "-DREACHABILITY",
                        ]
                    ).bind(  # pyright: ignore[reportUnknownMemberType]
                        lambda reachability_out: IOResult.from_result(
                            parser.check_reachability(reachability_out)
                        ).bind(  # pyright: ignore[reportUnknownMemberType]
                            lambda _: IOSuccess(
                                CbmcVerificationReport(
                                    file_path=OUTPUT_FILE,
                                    c_code=c_code,
                                    bound=bound,
                                    correctness_output=correctness_out,
                                    reachability_output=reachability_out,
                                )
                            )
                        )
                    )
                )
            )
        )
    )

    return result
