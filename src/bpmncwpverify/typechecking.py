from returns.result import Failure, Result, Success
from typing import Final, Callable

from bpmncwpverify.error import (
    Error,
    TypingAssignCompatabilityError,
    TypingNoTypeError,
)

# from bpmncwpverify.typing import BIT

BIT: Final[str] = "bit"
BOOL: Final[str] = "bool"
BYTE: Final[str] = "byte"
ENUM: Final[str] = "enum"
SHORT: Final[str] = "short"
INT: Final[str] = "int"

BYTEMIN: Final[int] = 0
BYTEMAX: Final[int] = 255
SHORTMIN: Final[int] = -32768
SHORTMAX: Final[int] = 32767
INTMIN: Final[int] = -2147483648
INTMAX: Final[int] = 2147483647


def get_computation_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    if ltype == rtype:
        return Success(ltype)
    elif "int" in [ltype, rtype]:
        return Success("int")
    elif "short" in [ltype, rtype]:
        return Success("short")
    return Failure(error(ltype, rtype))


def get_type_assign(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    if ltype == rtype:
        return Success(ltype)
    if ltype == BYTE and (rtype == BIT):
        return Success(ltype)
    if ltype == SHORT and (rtype == BIT or rtype == BYTE):
        return Success(ltype)
    if ltype == INT and (rtype == BIT or rtype == BYTE or rtype == SHORT):
        return Success(ltype)
    return Failure(error(ltype, rtype))


def get_type_literal(literal: str) -> Result[str, TypingNoTypeError]:
    if literal == "false" or literal == "true":
        return Success(BOOL)

    try:
        value: int = int(literal)
        if value == 0 or value == 1:
            return Success(BIT)
        if BYTEMIN <= value and value <= BYTEMAX:
            return Success(BYTE)
        if SHORTMIN <= value and value <= SHORTMAX:
            return Success(SHORT)
        if INTMIN <= value and value <= INTMAX:
            return Success(INT)
        return Failure(TypingNoTypeError(literal))
    except Exception:
        return Failure(TypingNoTypeError(literal))
