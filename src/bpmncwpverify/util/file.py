from pathlib import Path
from typing import TextIO, cast
from xml.etree.ElementTree import Element

from defusedxml import ElementTree
from returns.io import IOResult, IOResultE, impure_safe
from returns.pipeline import flow, managed
from returns.result import ResultE

from bpmncwpverify.core.error import (
    Error,
    FileReadFileError,
    FileWriteFileError,
    FileXmlParseError,
)


def _close_file(
    file_obj: TextIO,
    file_contents: ResultE[str | None],
) -> IOResultE[None]:
    return impure_safe(file_obj.close)()


def _read_file_contents(name: str) -> IOResult[str, Error]:
    io_result: IOResultE[str] = flow(
        name,
        impure_safe(_open_file_for_reading),
        managed(_read_file, _close_file),
    )

    def _exception_to_read_file_error(exc: Exception) -> Error:
        return FileReadFileError(str(exc))

    return io_result.alt(_exception_to_read_file_error)


def _open_file_for_reading(filename: str) -> TextIO:
    return open(filename)


def _open_file_for_writing(filename: str) -> TextIO:
    path = Path(filename)
    path.parent.mkdir(parents=True, exist_ok=True)
    return path.open("w")


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def _write_file(file_obj: TextIO, contents: str) -> IOResultE[None]:
    return impure_safe(file_obj.write)(contents).map(lambda _: None)


def element_tree_from_string(input: str) -> IOResult[Element, Error]:
    def _element_tree_from_string(input: str) -> Element:
        # defusedxml.ElementTree.fromstring is untyped, and pyright resolves it
        # differently depending on whether site-packages is on its path: as
        # Element[str] (cast looks unnecessary) or Unknown (cast is required to
        # avoid reportUnknownVariableType). The cast makes the type known in
        # both cases; suppress both environment-specific diagnostics.
        return cast(Element, ElementTree.fromstring(input))  # pyright: ignore[reportUnknownMemberType, reportUnnecessaryCast]

    def _exception_to_xml_parsing_error(exc: Exception) -> Error:
        return FileXmlParseError(str(exc))

    return (impure_safe(_element_tree_from_string)(input)).alt(
        lambda exc: _exception_to_xml_parsing_error(exc)
    )


def read_file_as_string(path: str) -> IOResult[str, Error]:
    return _read_file_contents(path)


def write_file_contents(contents: str, path: str) -> IOResult[None, Error]:
    result: IOResultE[None] = flow(
        path,
        impure_safe(_open_file_for_writing),
        managed(lambda f: _write_file(f, contents), _close_file),
        lambda result: result.map(lambda _: None),  # pyright: ignore[reportOptionalCall, reportUnknownLambdaType]
    )

    return result.alt(lambda exc: FileWriteFileError(str(exc)))
