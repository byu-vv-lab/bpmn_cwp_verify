from bpmncwpverify.core.error import Error
from bpmncwpverify.util.stringmanager import StringManager, NL_SINGLE
from typing import Type

import json
import subprocess


class ErrorTrace:
    """
    Class to represent an error trace.
    """

    def __init__(self, id: str, changed_vars: list[str], curr_cwp_state: list[str]):
        self.id = id
        self.changed_vars = changed_vars
        self.curr_cwp_state = curr_cwp_state


class CounterExample:
    """
    Class to represent a counterexample.
    """

    def __init__(self, trace_steps: list[ErrorTrace], error: Type["Error"]):
        self.trace_steps = trace_steps
        self.error = error.__name__

    def to_json(self) -> str:
        """
        Convert the counterexample to a JSON-compatible dictionary.
        """
        format = {
            "error": str(self.error),
            "trace_steps": [
                {
                    "id": step.id,
                    "changed_vars": step.changed_vars,
                    "curr_cwp_state": step.curr_cwp_state,
                }
                for step in self.trace_steps
            ],
        }
        return json.dumps(format, indent=4)

    @staticmethod
    def generate_counterexample(
        file_path: str, error: Type["Error"]
    ) -> "CounterExample":
        """
        Generate a counterexample from the given file path and error.
        """
        spin_trace_string = subprocess.run(
            ["spin", "-t", file_path], capture_output=True, text=True
        ).stdout
        filtered_str = CounterExample.filter_spin_trace(spin_trace_string)
        steps = CounterExample.extract_steps(filtered_str)

        return CounterExample(steps, error)

    @staticmethod
    def filter_spin_trace(spin_trace_string: str) -> str:
        """
        Filter the spin trace string and return a string.
        """
        lines = spin_trace_string.splitlines()
        filtered_str = StringManager()
        for line in lines:
            if line.startswith("spin:"):
                break
            else:
                filtered_str.write_str(line, NL_SINGLE)
        return str(filtered_str)

    @staticmethod
    def extract_steps(filtered_str: str) -> list[ErrorTrace]:
        """
        Extract trace steps from the filtered string.
        """
        lines = filtered_str.splitlines()
        steps = []
        line_index = 0
        while line_index < len(lines):
            id = ""
            changed_vars = []
            curr_cwp_state = []
            if lines[line_index].startswith("ID:"):
                id = lines[line_index].split(" ", 1)[1].strip()
                line_index += 1
                assert line_index < len(
                    lines
                ), "line_index should never be out of bounds"
                if lines[line_index].startswith("Changed vars:"):
                    line_index += 1
                    assert line_index < len(
                        lines
                    ), "line_index should never be out of bounds"
                    while not lines[line_index].startswith("Current state:"):
                        changed_vars.append(lines[line_index].strip())
                        line_index += 1
                        assert line_index < len(
                            lines
                        ), "line_index should never be out of bounds"
                    while line_index < len(lines) and lines[line_index].startswith(
                        "Current state:"
                    ):
                        curr_cwp_state.append(
                            lines[line_index].split(" ", 2)[2].strip()
                        )
                        line_index += 1
                steps.append(ErrorTrace(id, changed_vars, curr_cwp_state))
            else:
                line_index += 1
                assert line_index < len(
                    lines
                ), "line_index should never be out of bounds"
        return steps
