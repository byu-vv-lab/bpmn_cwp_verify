"""
cbmc_trip_count.py — derive how many times a counter-driven loop actually runs.

`compute_bound` sees graph shape only, so it has to guess a trip count for every
loop. That guess is wrong whenever the trip count is fixed by data rather than by
structure: simple_example's `x <= 5` loop needs six firings of its task, not the
default two, because `x` starts at 0 and the task adds 1 each pass.

This module recovers the count for the one shape that is worth recognising — a
loop guarded by an integer comparison against a variable the body changes by a
constant each pass:

    guard    x <= 5          (on the back-edge's sequence flow)
    body     (x, [x], x + 1) (a task behavior inside the loop)
    initial  var x: int = 0  (from the state file)
    =>       5 extra trips

Anything else returns None and the caller falls back to its default. Being
unable to derive a count is the normal case, not an error.
"""

import operator
from collections.abc import Callable, Iterable

from bpmncwpverify.core.bpmn import Node
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.feel_tree import (
    AddNode,
    ComparisonOperatorNode,
    ExpressionNode,
    GENode,
    GTNode,
    LENode,
    LTNode,
    NumberLiteralNode,
    QualifiedNameNode,
    SubtractNode,
    TripleListNode,
    TripleNode,
)
from bpmncwpverify.core.state import State

# Equality is deliberately absent: `x == 5` does not describe a counter loop.
_COMPARATORS: dict[type[ExpressionNode], Callable[[int, int], bool]] = {
    LTNode: operator.lt,
    LENode: operator.le,
    GTNode: operator.gt,
    GENode: operator.ge,
}

# A loop that appears to run more times than this is treated as underivable
# rather than trusted — the bound it implies would be unusable for CBMC anyway.
MAX_DERIVED_TRIPS = 1000


def _literal(node: ExpressionNode) -> int | None:
    if not isinstance(node, NumberLiteralNode):
        return None
    try:
        return int(node.value)
    except ValueError:  # a float literal is not a loop counter
        return None


def _name(node: ExpressionNode) -> str | None:
    return node.name if isinstance(node, QualifiedNameNode) else None


def _guard_terms(
    ast: ExpressionNode,
) -> tuple[str, Callable[[int, int], bool], int] | None:
    """`var OP literal` -> (var, predicate, literal). Also accepts `literal OP var`."""
    if not isinstance(ast, ComparisonOperatorNode):
        return None
    compare = _COMPARATORS.get(type(ast))
    if compare is None:
        return None

    var, limit = _name(ast.left), _literal(ast.right)
    if var is not None and limit is not None:
        return var, compare, limit

    # Mirrored form: `5 >= x` means the same as `x <= 5`.
    var, limit = _name(ast.right), _literal(ast.left)
    if var is not None and limit is not None:
        return var, lambda value, bound: compare(bound, value), limit

    return None


def _step(value: ExpressionNode, var: str) -> int | None:
    """Constant change `var` undergoes in `var + c`, `c + var` or `var - c`."""
    if isinstance(value, AddNode):
        if _name(value.left) == var:
            return _literal(value.right)
        if _name(value.right) == var:
            return _literal(value.left)
    if isinstance(value, SubtractNode) and _name(value.left) == var:
        amount = _literal(value.right)
        return None if amount is None else -amount
    return None


def _triples(ast: ExpressionNode) -> list[TripleNode]:
    if isinstance(ast, TripleListNode):
        return ast.triples
    return [ast] if isinstance(ast, TripleNode) else []


def _body_step(body: Iterable[Node], var: str) -> int | None:
    """Net constant change to `var` per pass, or None if the body is not linear in it."""
    total = 0
    assigned = False
    for node in body:
        behavior: Feel | None = getattr(node, "behavior", None)
        if behavior is None:
            continue
        for triple in _triples(behavior.ast):
            if _name(triple.target) != var:
                continue
            step = _step(triple.value, var)
            if step is None:
                return None  # writes var, but not by a constant
            total += step
            assigned = True
    return total if assigned else None


def _initial_value(state: State, var: str) -> int | None:
    for declared in state.vars:
        if declared.id == var:
            try:
                return int(declared.init.value)
            except (TypeError, ValueError):
                return None
    return None


def loop_trip_count(
    guard: Feel | None, body: Iterable[Node], state: State | None
) -> int | None:
    """
    Extra traversals a counter loop needs, beyond the one the acyclic path pays for.

    Returns None whenever the loop is not a recognisable counter — no guard, a
    non-integer comparison, a body that does not move the guard variable by a
    constant, or a count large enough to be suspect.
    """
    if guard is None or state is None:
        return None

    terms = _guard_terms(guard.ast)
    if terms is None:
        return None
    var, still_looping, limit = terms

    step = _body_step(body, var)
    if not step:  # unknown, or a body that never moves the variable
        return None

    value = _initial_value(state, var)
    if value is None:
        return None

    # The acyclic path already runs the body once before the guard is first read.
    value += step
    trips = 0
    while still_looping(value, limit):
        trips += 1
        if trips > MAX_DERIVED_TRIPS:
            return None
        value += step
    return trips
