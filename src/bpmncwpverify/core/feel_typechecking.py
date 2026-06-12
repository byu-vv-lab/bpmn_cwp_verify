from collections.abc import Callable
from typing import Final

from returns.result import Failure, Result, Success

from bpmncwpverify.core.error import (
    Error,
    TypingAssignCompatabilityError,
    TypingNoTypeError,
)

# from bpmncwpverify.typing import BIT

NUMBER: Final[str] = "number"
BOOL: Final[str] = "bool"

NUMBERMIN: Final[int] = -2147483648
NUMBERMAX: Final[int] = 2147483647


def get_and_or_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    if ltype == BOOL and rtype == BOOL:
        return Success(BOOL)
    return Failure(error(ltype, rtype))


def get_computation_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    if ltype in {BOOL} or rtype in {BOOL}:
        return Failure(error(ltype, rtype))
    elif ltype == rtype:
        return Success(ltype)
    elif "number" in [ltype, rtype]:
        return Success("int")
    return Failure(error(ltype, rtype))


def get_relational_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    similar_mapping = {
        "number": "number",
        "bool": "boolean",
    }

    if ltype == rtype or similar_mapping[ltype] == similar_mapping[rtype]:
        return Success(BOOL)

    return Failure(error(ltype, rtype))


def get_type_assign(ltype: str, rtype: str) -> Result[str, Error]:
    if ltype == rtype:
        return Success(ltype)
    # if ltype == BYTE and (rtype == BIT):
    #     return Success(ltype)
    # if ltype == SHORT and (rtype == BIT or rtype == BYTE):
    #     return Success(ltype)
    # if ltype == INT and (rtype == BIT or rtype == BYTE or rtype == SHORT):
    #     return Success(ltype)
    return Failure(TypingAssignCompatabilityError(ltype, rtype))


def get_type_literal(literal: str) -> Result[str, TypingNoTypeError]:
    if literal == "false" or literal == "true":
        return Success(BOOL)

    try:
        value: int = int(literal)
        if NUMBERMIN <= value and value <= NUMBERMAX:
            return Success(NUMBER)
        return Failure(TypingNoTypeError(literal))
    except Exception:
        return Failure(TypingNoTypeError(literal))
