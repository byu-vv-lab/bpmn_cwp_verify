import pytest
from unittest import mock

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
        BpmnFlowNoIdError(mock.Mock(attrib="test_attrib")),
        "Flow error: Flow_id does not exist. Occurred at tree element with following attributes: test_attrib.",
    ),
    (
        BpmnFlowOutgoingError("node_id"),
        "Flow error: All flow objects other than end events and compensating activities must have an outgoing sequence flow, if the process level includes any start or end events. node: node_id",
    ),
    (
        BpmnFlowStartEventError("node_id"),
        "Flow error: A start event cannot have an incoming sequence flow and cannot have an outgoing message flow. node: node_id",
    ),
    (
        BpmnFlowTypeError("flow_id"),
        "Flow error: Flow 'flow_id' is not a sequence flow when it should be.",
    ),
    (
        BpmnGraphConnError(),
        "Bpmn Process graph error: Process graph is not fully connected.",
    ),
    (
        BpmnInvalidIdError("bpmn_id"),
        "Bpmn id error: the bpmn element with id:bpmn_id contains an unsupported character (probably white space).",
    ),
    (
        BpmnMissingEventsError(1, 2),
        "Event error: Start events = 1, End events = 2. Missing required start or end events.",
    ),
    (
        BpmnMsgEndEventError("event_id"),
        "Message flow error: End events cannot have incoming messages. Event ID: event_id.",
    ),
    (
        BpmnMsgFlowSamePoolError("msg_id"),
        "Message flow error: msg_id connects nodes in the same pool.",
    ),
    (
        BpmnMsgGatewayError("gateway_type", "gateway_id"),
        "Gateway error: gateway_type gateways cannot have incoming or outgoing messages. Gateway ID: gateway_id.",
    ),
    (
        BpmnMsgMissingRefError("msg_id"),
        "Message flow error: Source ref or target ref is missing for message 'msg_id'.",
    ),
    (
        BpmnMsgNodeTypeError("msg_id"),
        "Message flow error: 'From' node and 'To' node of message are not of type Node. Message flow id: msg_id.",
    ),
    (
        BpmnMsgSrcError("obj_type", "node_id"),
        "Message flow source error while visiting obj_type. A message flow can only come from specific sources. Node ID: node_id.",
    ),
    (
        BpmnMsgStartEventError("node_id"),
        "Message flow error: A start event with incoming message flow must have a Message trigger. node: node_id",
    ),
    (
        BpmnMsgTargetError("obj_type", "node_id"),
        "Message flow target error while visiting obj_type. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool. Node ID: node_id.",
    ),
    (
        BpmnNodeTypeError("flow_id"),
        "Node type error: Source or target node of flow is not of type node. Flow details: flow_id.",
    ),
    (
        BpmnSeqFlowEndEventError("event_id"),
        "Sequence flow error: End event 'event_id' cannot have outgoing sequence flows.",
    ),
    (
        BpmnSeqFlowNoExprError("gateway_id", "out_flow_id"),
        "Flow: `out_flow_id` does not have an expression. All flows coming out of gateways must have expressions. Gateway id: gateway_id",
    ),
    (
        BpmnStructureError("node_id", "error_msg"),
        "BPMN ERROR at node: node_id. error_msg",
    ),
    (
        BpmnTaskFlowError("task_id"),
        "Task flow error: Task 'task_id' should have at least one incoming and one outgoing flow.",
    ),
    (
        CwpEdgeNoParentExprError(mock.Mock(attrib="edge_attrib")),
        "CWP ERROR: Expression or parent node not found in edge. Edge details: edge_attrib.",
    ),
    (
        CwpEdgeNoStateError(mock.Mock(attrib="edge_attrib")),
        "CWP ERROR: Edge does not have a source or a target. Edge details: edge_attrib.",
    ),
    (
        CwpFileStructureError("element"),
        "A element element is missing from your cwp file.",
    ),
    (
        CwpGraphConnError(),
        "CWP ERROR: Graph is not connected.",
    ),
    (
        CwpMultStartStateError(["first", "second"]),
        "CWP ERROR: More than one start state found. Start state IDs: ['first', 'second'].",
    ),
    (
        CwpNoEndStatesError(),
        "CWP ERROR: No end states found.",
    ),
    (
        CwpNoParentEdgeError("parent_edge"),
        "CWP ERROR: Parent edge not found or no parent ID reference. Edge details: parent_edge.",
    ),
    (
        CwpNoStartStateError(),
        "CWP ERROR: No start states found.",
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
    "BpmnFlowNoIdError",
    "BpmnFlowOutgoingError",
    "BpmnFlowStartEventError",
    "BpmnFlowTypeError",
    "BpmnGraphConnError",
    "BpmnInvalidIdError",
    "BpmnMissingEventsError",
    "BpmnMsgEndEventError",
    "BpmnMsgFlowSamePoolError",
    "BpmnMsgGatewayError",
    "BpmnMsgMissingRefError",
    "BpmnMsgNodeTypeError",
    "BpmnMsgSrcError",
    "BpmnMsgStartEventError",
    "BpmnMsgTargetError",
    "BpmnNodeTypeError",
    "BpmnSeqFlowEndEventError",
    "BpmnSeqFlowNoExprError",
    "BpmnStructureError",
    "BpmnTaskFlowError",
    "CwpEdgeNoParentExprError",
    "CwpEdgeNoStateError",
    "CwpFileStructureError",
    "CwpGraphConnError",
    "CwpMultStartStateError",
    "CwpNoEndStatesError",
    "CwpNoParentEdgeError",
    "CwpNoStartStateError",
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
