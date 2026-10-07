import argparse
import json
import logging
from typing import Any

from returns.functions import not_
from returns.io import IOFailure, IOResult, IOSuccess
from returns.pipeline import is_successful

from bpmncwpverify.core.error import Error, FileReadFileError

logging.basicConfig(level=logging.INFO)


class TraceStep:
    id: str
    changed_vars: list[str]
    cur_cwp_state: list[str]

    def __init__(self, id: str, changed_vars: list[str], cur_cwp_state: list[str]):
        self.id = id
        self.changed_vars = changed_vars
        self.cur_cwp_state = cur_cwp_state

    def __str__(self) -> str:
        return f"TraceStep(id={self.id}, changed_vars={self.changed_vars}, cur_cwp_state={self.cur_cwp_state})"


class SpinErrorLog:
    error: str
    issue: str
    init_variables: list[str]
    trace_steps: list[TraceStep]

    def __init__(
        self,
        error: str,
        issue: str,
        init_variables: list[str],
        trace_steps: list[TraceStep],
    ):
        self.error = error
        self.issue = issue
        self.init_variables = init_variables
        self.trace_steps = trace_steps

    def __str__(self) -> str:
        return f"SpinErrorLog(\n    error={self.error}, \n    issue={self.issue}, \n    init_variables={self.init_variables}, \n    trace_steps={[str(step) for step in self.trace_steps]}\n)"


def _get_argument_parser() -> "argparse.ArgumentParser":
    argument_parser = argparse.ArgumentParser(
        description="Visualize the counter example from a cwp and bpmn verification."
    )

    argument_parser.add_argument(
        "counter_example_file",
        help="Visual mermaid file of the counter example",
    )

    argument_parser.add_argument(
        "trace_file",
        help="Steps of the counter example",
    )

    return argument_parser


def _print_result(result: IOResult[Any, Error]) -> None:
    if not_(is_successful)(result):
        logging.info(result.unwrap())
    else:
        logging.info("Successfully ran and exited.")


def _vce(counter_example_file: str, trace_file: str) -> IOResult[Any, Error]:
    return _read_inputs(counter_example_file, trace_file).bind(  # pyright: ignore[reportUnknownMemberType]
        lambda x: _repl(x[0], x[1])
    )


def _repl(
    counter_example_file: str, spin_error_log: SpinErrorLog
) -> IOResult[Any, Error]:
    current_step = -1
    print(
        "Starting counter example visualization. Please open the mermaid preview for the counter exmaple. Type 'h' for help."
    )
    print(f"Total steps: {len(spin_error_log.trace_steps)}")
    try:
        with open(counter_example_file, "a+") as counter_example:
            counter_example.write("Debug\n")
            counter_example.write("note right of Debug\n")
            counter_example.write("    Current CWP State:\n")
            counter_example.write("end note\n")
            counter_example.write("note right of Debug\n")
            counter_example.write("    Changed Vars:\n")
            counter_example.write("end note\n")
            counter_example.flush()
            while True:
                command = input("Command: ").strip().lower()
                if command == "n":
                    if current_step < len(spin_error_log.trace_steps) - 1:
                        current_step += 1
                    else:
                        print("Already at the last step.")
                elif command == "p":
                    if current_step > -1:
                        current_step -= 1
                    else:
                        print("Already at the first step.")
                elif command == "q":
                    break
                elif command == "h":
                    print("List of Commands:")
                    print("  n - next step")
                    print("  p - previous step")
                    print("  q - quit")
                    print("  h - help")
                else:
                    print("Unknown command. Type 'h' for help.")
    except FileNotFoundError as e:
        return IOFailure(
            FileReadFileError(f"Failed to open {counter_example_file}. {e}")
        )

    return IOSuccess(None)


def _read_inputs(
    counter_example_file: str, trace_file: str
) -> IOResult[tuple[str, SpinErrorLog], Error]:
    logging.info("Opening counter example and trace files 0/2")

    logging.info(f"    Reading file: {counter_example_file}")
    try:
        with open(counter_example_file) as file:
            logging.info(f"    Successfully read file: {counter_example_file}")
    except Exception as e:
        return IOFailure(
            FileReadFileError(f"Failed to read {counter_example_file} file. {e}")
        )

    logging.info(f"    Reading file: {trace_file}")
    try:
        with open(trace_file) as file:
            data = json.load(file)
            data = SpinErrorLog(**data)
            logging.info(data)
            logging.info(f"    Successfully read file: {trace_file}")
    except Exception as e:
        return IOFailure(FileReadFileError(f"Failed to read {trace_file} file. {e}"))

    return IOSuccess((counter_example_file, data))


# Takes mermaid file and trace file generated by a counter exmaple
# and allows user to move through steps of the file
def vce() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()

    _print_result(_vce(args.counter_example_file, args.trace_file))
