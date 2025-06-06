from returns.result import Result, Success, Failure
from typing import Dict, List
from bpmncwpverify.core.error import (
    Error,
    SpinSyntaxError,
    SpinInvalidEndStateError,
    SpinAssertionError,
    SpinCoverageError,
    get_error_message,
)
from bpmncwpverify.core.counterexample import CounterExample
import subprocess
import re
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.curry import partial
import os


class CoverageReport:
    def __init__(self, full_spin_output: str) -> None:
        self.full_spin_output = full_spin_output


class SpinOutput:
    def _get_re_matches(self, regex: str, spin_msg: str) -> List[Dict[str, str]]:
        r = re.compile(regex)

        return [
            {k: re.sub(r"\s+", " ", v).strip() for k, v in t.groupdict().items()}
            for t in r.finditer(spin_msg)
        ]

    def _check_invalid_end_state(
        self, file_path: str, spin_msg: str
    ) -> Result[str, Error]:
        errors = self._get_re_matches(r"invalid end state \((?P<info>.*)\)", spin_msg)

        counter_example = CounterExample.generate_counterexample(
            file_path, SpinAssertionError
        )

        return (
            Failure(SpinInvalidEndStateError(counter_example.to_json(), errors))
            if errors
            else Success(spin_msg)
        )

    def _check_assertion_violation(
        self, file_path: str, spin_msg: str
    ) -> Result[str, Error]:
        errors = self._get_re_matches(
            r"assertion violated \(?(?P<assertion>[^\s)]*)\)? (?P<depth>.*)", spin_msg
        )

        counter_example = CounterExample.generate_counterexample(
            file_path, SpinAssertionError
        )

        return (
            Failure(SpinAssertionError(counter_example.to_json(), errors))
            if errors
            else Success(spin_msg)
        )

    def _check_syntax_errors(self, file_path: str, spin_msg: str) -> Result[str, Error]:
        errors = self._get_re_matches(
            r"spin: (?P<file_path>.*?):(?P<line_number>\d+),\sError: (?P<error_msg>.*)",
            spin_msg,
        )

        counter_example = CounterExample.generate_counterexample(
            file_path, SpinAssertionError
        )

        return (
            Failure(SpinSyntaxError(counter_example.to_json(), errors))
            if errors
            else Success(spin_msg)
        )

    def _check_coverage_errors(
        self, file_path: str, spin_msg: str
    ) -> Result[str, Error]:
        # Regular expression to match proctype and init blocks, excluding never claims
        block_pattern = re.compile(
            r"unreached in (?:proctype (?P<proctype>\w+)|(?P<init>init))\n(?P<body>(?:\s+[^\n]+(?!\s+unreached))+)"
        )

        # Regular expression to match line information
        line_pattern = re.compile(
            r"(?P<file>[\w\.]+):(?P<line>\d+), state \d+, (?P<message>\"(?!.*assert).*?\")"
        )

        # Find all relevant blocks (excluding never claims)
        matches = block_pattern.finditer(spin_msg)

        detailed_errors: List[Dict[str, str]] = []

        for match in matches:
            proctype_name = (
                match.group("proctype") if match.group("proctype") else "init"
            )

            lines_block = match.group("body")  # Extract only the lines within the block

            for line_match in line_pattern.finditer(lines_block):
                file_name = line_match.group("file")
                line_number = line_match.group("line")
                message = line_match.group("message")

                detailed_errors.append(
                    {
                        "proctype": proctype_name,
                        "file": file_name,
                        "line": line_number,
                        "message": message,
                    }
                )

        counter_example = CounterExample.generate_counterexample(
            file_path, SpinAssertionError
        )

        return (
            Failure(SpinCoverageError(counter_example.to_json(), detailed_errors))
            if detailed_errors
            else Success(spin_msg)
        )

    @staticmethod
    def get_spin_output(file_path: str) -> Result[CoverageReport, str]:
        file_dir = os.path.dirname(file_path)

        spin_run_string = subprocess.run(
            ["spin", "-run", "-noclaim", os.path.basename(file_path)],
            capture_output=True,
            text=True,
            cwd=file_dir,  # This ensures the .trail is written in the same directory as file_path
        ).stdout

        spin_output = SpinOutput()

        result: Result[str, Error] = flow(
            spin_run_string,
            partial(spin_output._check_syntax_errors, file_path),
            bind_result(partial(spin_output._check_invalid_end_state, file_path)),
            bind_result(partial(spin_output._check_assertion_violation, file_path)),
            bind_result(partial(spin_output._check_coverage_errors, file_path)),
        )

        if is_successful(result):
            return Success(CoverageReport(spin_run_string))

        error: Error = result.failure()
        msg: str = get_error_message(error)
        return Failure(msg)
