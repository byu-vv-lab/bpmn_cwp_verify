from enum import Enum
from typing import Union

NL_NONE = 0
NL_SINGLE = 1
NL_DOUBLE = 2


class IndentAction(Enum):
    NIL = 0
    INC = 1
    DEC = 2
    DECTWO = 3


class StringManager:
    __slots__ = ["contents", "indent"]

    def __init__(self) -> None:
        # (indent_level, text)
        self.contents: list[tuple[int, str]] = []
        self.indent = 0

    def _tab(self) -> str:
        """return string contianing 'self.indent' tabs"""
        return "\t" * self.indent

    def _newline(self, nl: int) -> str:
        """Return string containing 'nl' new lines."""
        return "\n" * nl

    def _inc_indent(self) -> None:
        self.indent += 1

    def _dec_indent(self) -> None:
        assert self.indent > 0
        self.indent -= 1

    def _dectwo_indent(self) -> None:
        assert self.indent > 1
        self.indent -= 2

    def write_str(
        self,
        new_str: Union[str, "StringManager"],
        nl: int = NL_NONE,
        indent_action: IndentAction = IndentAction.NIL,
        indent_offset: int = 0,
    ) -> None:
        """
        Add a string or another StringManager.

        indent_offset is only used when inserting another
        StringManager and allows rebasing its indentation.
        """

        if indent_action == IndentAction.DEC:
            self._dec_indent()

        elif indent_action == IndentAction.DECTWO:
            self._dectwo_indent()

        if isinstance(new_str, StringManager):
            if nl != NL_NONE:
                raise ValueError("nl cannot be used when appending a StringManager")

            for indent, text in new_str.contents:
                self.contents.append((indent + indent_offset, text))

        else:
            text = new_str + ("\n" * nl)
            self.contents.append((self.indent, text))

        if indent_action == IndentAction.INC:
            self._inc_indent()

    def __str__(self) -> str:
        result: list[str] = []
        at_line_start = True

        for indent, text in self.contents:
            if at_line_start:
                result.append("\t" * indent)
                at_line_start = False

            result.append(text)

            if text.endswith("\n"):
                at_line_start = True

        return "".join(result)

    def __repr__(self) -> str:
        return str(self)
