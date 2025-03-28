import pytest

from returns.maybe import Some, Nothing

from bpmncwpverify.core.error import (
    Error,
    BpmnFlowIncomingError,
    BpmnFlowNoIdError,
    BpmnFlowOutgoingError,
    BpmnFlowStartEventError,
    BpmnFlowTypeError,
    BpmnGraphConnError,
    BpmnInvalidIdError,
    BpmnMissingEventsError,
    BpmnMsgEndEventError,
    BpmnMsgFlowSamePoolError,
    BpmnMsgGatewayError,
    BpmnMsgMissingRefError,
    BpmnMsgNodeTypeError,
    BpmnMsgSrcError,
    BpmnMsgStartEventError,
    BpmnMsgTargetError,
    BpmnNodeTypeError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnStructureError,
    BpmnTaskFlowError,
    CwpEdgeNoParentExprError,
    CwpEdgeNoStateError,
    CwpFileStructureError,
    CwpGraphConnError,
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoParentEdgeError,
    CwpNoStartStateError,
    Error,
    ExpressionComputationCompatabilityError,
    ExpressionNegatorError,
    ExpressionRelationCompatabilityError,
    ExpressionRelationalNotError,
    ExpressionUnrecognizedID,
    MessageError,
    MissingFileError,
    NotImplementedError,
    SpinAssertionError,
    SpinCoverageError,
    SpinInvalidEndStateError,
    SpinSyntaxError,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
    TypingAssignCompatabilityError,
    TypingNoTypeError,
    get_error_message,
)

test_inputs: list[tuple[Error, str]] = [
    (
        BpmnFlowIncomingError("node_id"),
        "Flow error: All flow objects other than start events, boundary events, and compensating activities must have an incoming sequence flow, if the process level includes any start or end events. node: node_id.",
    ),
    (
        BpmnStructureError("node_id", "error_msg"),
        "BPMN ERROR at node: node_id. error_msg",
    ),
    (NotImplementedError("notImplemented"), "ERROR: not implemented 'notImplemented'"),
    (
        StateInitNotInValues("a", Some(0), Some(1), {"b", "c"}),
        "STATE ERROR: init value 'a' at line 0:1 not in allowed values ['b', 'c']",
    ),
    (
        StateInitNotInValues("a", Nothing, Nothing, {"b", "c"}),
        "STATE ERROR: init value 'a' not in allowed values ['b', 'c']",
    ),
    (
        StateMultipleDefinitionError("a", Nothing, Nothing, Nothing, Nothing),
        "STATE ERROR: multiple definition of 'a'",
    ),
    (
        StateMultipleDefinitionError("a", Some(42), Some(43), Nothing, Nothing),
        "STATE ERROR: multiple definition of 'a' at line 42:43",
    ),
    (
        StateMultipleDefinitionError("a", Some(42), Some(43), Some(0), Some(1)),
        "STATE ERROR: multiple definition of 'a' at line 42:43, previously defined at line 0:1",
    ),
    (StateSyntaxError("bad syntax"), "STATE SYNTAX ERROR: bad syntax"),
    (
        TypingAssignCompatabilityError("enum", "int"),
        "TYPING ERROR: something of type 'int' cannot by assigned to something of type 'enum'",
    ),
    (TypingNoTypeError("a"), "TYPING ERROR: literal 'a' has an unknown type"),
]

test_ids: list[str] = [
    "BpmnFlowIncomingError",
    "BpmnStructureError",
    "NotImplementedError",
    "StateInitNotInValues",
    "StateInitNotInValuesLineCol",
    "StateMultipleDefinitionError",
    "StateMultipleDefinitionErrorLineCol",
    "StateMultipleDefinitionErrorLineColPrevLinePrevCol",
    "StateSyntaxError",
    "TypeingAssignCompatabilityError",
    "TypingNoTypeError",
]


@pytest.mark.parametrize(
    scope="function",
    argnames=["error", "expected"],
    argvalues=test_inputs,
    ids=test_ids,
)
def test_given_error_when_get_error_message_then_message_equals_expected(
    error: Error, expected: str
):
    # given
    # error

    # when
    result = get_error_message(error)

    # then
    assert expected == result
