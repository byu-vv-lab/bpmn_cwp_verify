from bpmncwpverify.core.error import (
    Error,
    TypingAssignCompatabilityError,
    TypingNoTypeError,
)

from returns.result import Failure, Result, Success
from typing import Final, Callable

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


def get_and_or_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    """
    Check type compatability for and/or expressions

    Args:
        ltype (str): Type left of the operator
        rtype (str): Type right of the operator
        error (Callable[[str,str], Error], optional): Error to call if check fails. Default to TypingAssignCompatabilityError
    """
    if ltype == BOOL and rtype == BOOL:
        return Success(BOOL)
    return Failure(error(ltype, rtype))


def get_computation_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    """
    Check type compatability for computation expressions

    Args:
        ltype (str): Type left of the operator
        rtype (str): Type right of the operator
        error (Callable[[str,str], Error], optional): Error to call if check fails. Default to TypingAssignCompatabilityError
    """
    if ltype in {BIT, BOOL} or rtype in {BIT, BOOL}:
        return Failure(error(ltype, rtype))
    elif ltype == rtype:
        return Success(ltype)
    elif "int" in [ltype, rtype]:
        return Success("int")
    elif "short" in [ltype, rtype]:
        return Success("short")
    return Failure(error(ltype, rtype))


def get_relational_type_result(
    ltype: str,
    rtype: str,
    error: Callable[[str, str], Error] = TypingAssignCompatabilityError,
) -> Result[str, Error]:
    """
    Check type compatability for relational expressions

    Args:
        ltype (str): Type left of the operator
        rtype (str): Type right of the operator
        error (Callable[[str,str], Error], optional): Error to call if check fails. Default to TypingAssignCompatabilityError
    """
    similar_mapping = {
        "bit": "number",
        "byte": "number",
        "short": "number",
        "int": "number",
        "bool": "boolean",
    }

    if ltype == rtype or similar_mapping[ltype] == similar_mapping[rtype]:
        return Success(BOOL)

    return Failure(error(ltype, rtype))


def get_type_assign(ltype: str, rtype: str) -> Result[str, Error]:
    """
    Check type compatabilty for variable assignment

    Args:
        ltype (str): Type left of variable assignment
        rtype (str): Type right of variable assignment
    """
    if ltype == rtype:
        return Success(ltype)
    if ltype == BYTE and (rtype == BIT):
        return Success(ltype)
    if ltype == SHORT and (rtype == BIT or rtype == BYTE):
        return Success(ltype)
    if ltype == INT and (rtype == BIT or rtype == BYTE or rtype == SHORT):
        return Success(ltype)
    return Failure(TypingAssignCompatabilityError(ltype, rtype))


def get_type_literal(literal: str) -> Result[str, TypingNoTypeError]:
    """
    Retrieve the literal type of the variable if it isn't an enum type

    Args:
        literal (str): Variable to check
    """
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
