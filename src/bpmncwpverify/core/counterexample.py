from bpmncwpverify.core.error import Error

import subprocess


class ErrorTrace:
    """
    Class to represent an error trace.
    """

    def __init__(self, id: str, changed_vars: list[str], curr_cwp_state: str):
        self.id = id
        self.changed_vars = changed_vars
        self.curr_cwp_state = curr_cwp_state


class CounterExample:
    """
    Class to represent a counterexample.
    """

    def __init__(self, trace_steps: list[ErrorTrace], error: Error):
        self.trace_steps = trace_steps
        self.error = error

    @staticmethod
    def generate_counterexample(file_path: str, error: Error) -> "CounterExample":
        """
        Generate a counterexample from the given file path and error.
        """
        spin_trace_string = subprocess.run(
            ["spin", "-t", file_path], capture_output=True, text=True
        ).stdout
        filtered_str = CounterExample.filter_spin_trace(spin_trace_string)  # noqa: F841

        return CounterExample([], error)

    @staticmethod
    def filter_spin_trace(spin_trace_string: str) -> str:
        """
        Filter the spin trace string and return a string.
        """
        lines = spin_trace_string.splitlines()
        filtered_str = ""
        for line in lines:
            if line.startswith("spin:"):
                break
            else:
                filtered_str += line + "\n"
        return filtered_str
