from typing import Optional, TextIO, cast
from xml.etree.ElementTree import Element

from defusedxml import ElementTree
from returns.io import IOResult, IOResultE, impure_safe
from returns.pipeline import flow, managed
from returns.result import ResultE

from bpmncwpverify.core.error import Error, MissingFileError, WriteFileError


def _close_file(
    file_obj: TextIO,
    file_contents: ResultE[Optional[str]],
) -> IOResultE[None]:
    return impure_safe(file_obj.close)()


def _read_file_contents(name: str) -> IOResult[str, Error]:
    io_result: IOResultE[str] = flow(
        name,
        impure_safe(_open_file_for_reading),
        managed(_read_file, _close_file),
    )

    def exception_to_missing_file_error(_: Exception) -> Error:
        return MissingFileError(name)

    return io_result.alt(exception_to_missing_file_error)


def _open_file_for_reading(filename: str) -> TextIO:
    return open(filename, "r")


def _open_file_for_writing(filename: str) -> TextIO:
    return open(filename, "w")


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def _write_file(file_obj: TextIO, contents: str) -> IOResultE[None]:
    return impure_safe(file_obj.write)(contents).map(lambda _: None)


def element_tree_from_string(input: str) -> Element:
    return cast(Element, ElementTree.fromstring(input))  # pyright: ignore[reportUnknownMemberType]


def read_file_as_string(path: str) -> IOResult[str, Error]:
    return _read_file_contents(path)


def read_file_as_xml(path: str) -> IOResult[Element, Error]:
    return _read_file_contents(path).map(element_tree_from_string)


def write_file_contents(contents: str, path: str) -> IOResult[None, Error]:
    result: IOResultE[None] = flow(
        path,
        impure_safe(_open_file_for_writing),
        managed(lambda f: _write_file(f, contents), _close_file),
        lambda result: result.map(lambda _: None),  # pyright: ignore[reportOptionalCall, reportUnknownLambdaType]
    )

    return result.alt(lambda exc: WriteFileError(str(exc)))
