from typing import List

from antlr4 import CommonTokenStream, InputStream
from antlr4.error.ErrorStrategy import ParseCancellationException
from bpmncwpverify.antlr.SpinLexer import SpinLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.core.error import Error, StateSyntaxError
from returns.maybe import Maybe
from returns.result import Failure, Result, Success
from bpmncwpverify.antlr.SpinListener import SpinListener
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
        ["spin", "-run", file_path], capture_output=True, text=True
    ).stdout
    return result


class Listener(SpinListener):  # type: ignore
    pass


def _get_parser(file_contents: str) -> Result[StateParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = SpinLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = StateParser(stream)
    return Success(parser)


def _parse_state(parser: StateParser) -> Result[StateParser.StateContext, Error]:
    try:
        tree: StateParser.StateContext = parser.state()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = StateSyntaxError(msg)
        return Failure(failure_value)


# _parse_state(_get_parser(get_spin_output(os.getcwd() + 'test/resources/simple_example/valid_output.pml')))
