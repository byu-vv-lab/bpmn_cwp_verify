# type: ignore
from unittest import mock

import pytest
from returns.maybe import Nothing, Some

from bpmncwpverify.core.error import (
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
    BpmnNoElementNameError,
    BpmnNoSwimLaneNameError,
    BpmnSeqFlowEndEventError,
    BpmnSeqFlowNoExprError,
    BpmnStructureError,
    BpmnTaskFlowError,
    BpmnUnrecognizedElement,
    BpmnUnsupportedStartEvent,
    CbmcAssertionError,
    CbmcReachabilityError,
    CbmcSubProcessError,
    CounterExampleError,
    CwpEdgeInvalidStateError,
    CwpEdgeNoExpressionError,
    CwpEdgeNoParentError,
    CwpEdgeNoStateError,
    CwpFileStructureError,
    CwpGraphConnError,
    CwpInvalidAssignmentError,
    CwpInvalidAssignmentTargetError,
    CwpInvalidLiteralError,
    CwpInvalidStartEdgeError,
    CwpInvalidStartExpressionError,
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoParentEdgeError,
    CwpNoStartStateError,
    CwpUnsupportedElementError,
    Error,
    ExpressionComputationCompatabilityError,
    ExpressionIfBranchCompatabilityError,
    ExpressionIfConditionError,
    ExpressionNegatorError,
    ExpressionOutOfScope,
    ExpressionParseError,
    ExpressionRelationalNotError,
    ExpressionRelationCompatabilityError,
    ExpressionTripleInputError,
    ExpressionUnrecognizedID,
    FileReadFileError,
    FileWriteFileError,
    FileXmlParseError,
    FlowExpressionError,
    MessageError,
    NotImplementedError,
    NotInitializedError,
    SpinAssertionError,
    SpinCoverageError,
    SpinInvalidEndStateError,
    SpinSyntaxError,
    StartExpressionDisallowedAssignemntError,
    StateAntlrWalkerError,
    StateArraySizeError,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
    SubProcessRunError,
    TypingAssignCompatabilityError,
    TypingListCompatibiltiyError,
    TypingListOfExpressionsError,
    TypingNoTypeError,
    TypingTripleVariableError,
    get_error_message,
)

test_inputs: list[tuple[Error, str]] = [
    (
        BpmnUnsupportedStartEvent("Event_342dt"),
        "Bpmn error: Event_342dt is not a supported start event",
    ),
    (
        BpmnNoElementNameError(["Event_4kd93"]),
        "Bpmn error: ['Event_4kd93'] must have a name that is different from their ID.",
    ),
    (
        BpmnNoSwimLaneNameError(["Proces_32kdf8"]),
        "Bpmn error: ['Proces_32kdf8'] must have a swimlane with a name that is different from their ID",
    ),
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
        BpmnUnrecognizedElement("element_name"),
        "BPMN ERROR: Unrecognized bpmn element type in workflow: element_name",
    ),
    (
        CwpEdgeInvalidStateError("edge_id"),
        "CWP ERROR: Edge has an invalid source or target. Edge name: edge_id.",
    ),
    (
        CwpEdgeNoParentError(mock.Mock(attrib="edge_attrib")),
        "CWP ERROR: Parent node not found in edge. Edge details: edge_attrib.",
    ),
    (
        CwpEdgeNoStateError(mock.Mock(attrib="edge_attrib")),
        "CWP ERROR: Edge does not have a source or a target. Edge details: edge_attrib.",
    ),
    (
        CwpEdgeNoExpressionError(mock.Mock(attrib="edge_attrib")),
        "CWP ERROR: Expression not found in edge. Edge details: edge_attrib.",
    ),
    (
        CwpUnsupportedElementError(2, "object"),
        "CWP ERROR: object is/are not supported and there exists 2",
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
        "CWP ERROR: No start state found.",
    ),
    (
        CwpInvalidLiteralError(),
        "CWP ERROR: Expression on start edge invalid type",
    ),
    (
        CwpInvalidStartEdgeError(),
        "CWP ERROR: Start edge invalid",
    ),
    (
        CwpInvalidStartExpressionError(),
        "CWP ERROR: Expression on start edge parsing incorrectly",
    ),
    (
        CwpInvalidAssignmentError(),
        "CWP ERROR: Start edge expression contains an invalid variable assignment",
    ),
    (
        CwpInvalidAssignmentTargetError(),
        "CWP ERROR: Start edge expression contains an invalid variable name",
    ),
    (
        ExpressionComputationCompatabilityError("ltype", "rtype"),
        "EXPR ERROR: something of type 'rtype' cannot be computed with something of type 'ltype'",
    ),
    (
        ExpressionNegatorError("_type"),
        "EXPR ERROR: sometiong of type '_type' cannot be used with a mathmatical negator",
    ),
    (
        ExpressionParseError("exception_str"),
        "Error while parsing expression: exception_str",
    ),
    (
        StartExpressionDisallowedAssignemntError("exception_str"),
        "Error wile parsing start edge expression: variable exception_str assigned to invalid value",
    ),
    (
        ExpressionRelationCompatabilityError("ltype", "rtype"),
        "EXPR ERROR: something of type 'rtype' cannot be related with something of type 'ltype'",
    ),
    (
        ExpressionIfBranchCompatabilityError("thentype", "elsetype"),
        "EXPR ERROR: if must have same or compatible return types on branchs,'thentype' and 'elsetype' are not compatible",
    ),
    (
        ExpressionIfConditionError("type"),
        "EXPR ERROR: if statement must have a conditional expression result in a bool, not a 'type'",
    ),
    (
        ExpressionRelationalNotError("_type"),
        "EXPR ERROR: something of type '_type' cannot be used with a relational not",
    ),
    (
        ExpressionUnrecognizedID("_id"),
        "EXPR ERROR: '_id' is not recognized as a literal or something stored in the symbol table",
    ),
    (
        ExpressionOutOfScope("id"),
        "EXPR ERROR: 'id' is out of scope",
    ),
    (
        ExpressionTripleInputError(),
        "EXPR ERROR: input in triple is not valid and can only be a list of varibles",
    ),
    (
        FileReadFileError("file_name"),
        "FILE ERROR: 'file_name'",
    ),
    (FileWriteFileError("a"), "FILE ERROR: 'a'"),
    (FileXmlParseError("a"), "FILE ERROR: 'a'"),
    (
        FlowExpressionError("flow_id", "expression", "exception_str"),
        "Error occurred while parsing the expression on flow: 'flow_id' with expression: 'expression':\n\t'exception_str'",
    ),
    (
        MessageError("node_id", "error_msg"),
        "Inter-process message error at node: node_id. error_msg",
    ),
    (NotImplementedError("notImplemented"), "ERROR: not implemented 'notImplemented'"),
    (
        SpinAssertionError(
            "",
            [
                {"assertion": "test_assertion1", "depth": "test_depth1"},
                {"assertion": "test_assertion2", "depth": "test_depth2"},
            ],
        ),
        "Assertion Error:\n2 error(s) occurred:\n1: Assertion: test_assertion1, Depth info: test_depth1\n2: Assertion: test_assertion2, Depth info: test_depth2\n",
    ),
    (NotInitializedError("x"), "ERROR: 'x' is not initialized"),
    (
        SpinCoverageError(
            [
                {
                    "proctype": "test_proctype",
                    "file": "test_file",
                    "line": "test_line",
                    "message": "test_message",
                }
            ],
        ),
        "Spin Coverage Error:\nProctype: test_proctype, File: test_file, Line: test_line, Message: test_message",
    ),
    (
        SpinInvalidEndStateError("", [{"info": "test_info1"}, {"info": "test_info2"}]),
        "Invalid end state\n2 error(s) occurred:\n1: test_info1\n2: test_info2\n",
    ),
    (
        SpinSyntaxError(
            [
                {
                    "line_number": "1",
                    "file_path": "test/file/path",
                    "error_msg": "test_msg",
                }
            ],
        ),
        "Syntax Error in generated promela:\n1 error(s) occurred:\n1: On line 1 in the file 'test/file/path': test_msg",
    ),
    (
        StateAntlrWalkerError("error"),
        "STATE ERROR: error",
    ),
    (
        StateArraySizeError("array_name", Some(0), Some(12), 5, 4),
        "STATE ARRAY SIZE ERROR: array 'array_name' at line 0:12 has size 4, expected size 5",
    ),
    (
        StateArraySizeError("array_name", Some(0), Some(12), 0, 0),
        "STATE ARRAY SIZE ERROR: array 'array_name' at line 0:12. Array size must be greater than 0.",
    ),
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
    (SubProcessRunError("proc"), "ERROR: failed to run 'proc'"),
    (
        TypingListCompatibiltiyError("first_type", "second_type"),
        "TYPING ERROR: list of type 'first_type' is not compatible with 'second_type'",
    ),
    (
        TypingListOfExpressionsError(),
        "TYPING ERROR: list has an expresssion that is not a number, bool, or variable and is not allowed",
    ),
    (
        TypingTripleVariableError("id"),
        "TYPING ERROR: 'id' is not a variable and cannot be used as input",
    ),
    (TypingNoTypeError("a"), "TYPING ERROR: literal 'a' has an unknown type"),
    (
        CbmcAssertionError(
            [
                "[update_cwp_state.assertion.1] line 83 CWP P1: transition follows valid CWP edge: FAILURE",
                "[main.unwind.0] unwinding assertion loop 0: FAILURE",
            ]
        ),
        "CBMC CORRECTNESS FAILURE (P1-P3):\n"
        "  2 failing assertion(s):\n"
        "  1. line 83: CWP P1: transition follows valid CWP edge\n"
        "  2. [main.unwind.0] unwinding assertion loop 0: FAILURE",
    ),
    (
        # Covers all three label branches: end-event goal ('Event_<id>_reached'),
        # CWP-state goal ('cwp_reached[...]'), and the unparseable fallback.
        CbmcReachabilityError(
            [
                "[main.coverage.1] file ./tmp/verification.c line 299 function main condition 'Event_1y6wxsp_reached != FALSE': FAILED",
                "[main.coverage.3] file ./tmp/verification.c line 301 function main condition 'cwp_reached[(signed long int)2] != FALSE': FAILED",
                "[main.coverage.9] FAILED",
            ]
        ),
        "CBMC REACHABILITY FAILURE (P4 - unreachable goals):\n"
        "  3 goal(s) not covered:\n"
        "  1. line 299: end event 'Event_1y6wxsp' unreachable\n"
        "  2. line 301: CWP state 2 unreachable\n"
        "  3. [main.coverage.9] FAILED",
    ),
    (
        CbmcSubProcessError("cbmc --cover"),
        "CBMC ERROR: failed to run 'cbmc --cover'",
    ),
]

test_ids: list[str] = [
    "BpmnUnsupportedStartEvent",
    "BpmnNoElementNameError",
    "BpmnNoSwimLaneNameError",
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
    "BpmnUnrecognizedElement",
    "CwpEdgeInvalidStateError",
    "CwpEdgeNoParentError",
    "CwpEdgeNoStateError",
    "CwpEdgeNoExpressionError",
    "CwpFileStructureError",
    "CwpGraphConnError",
    "CwpMultStartStateError",
    "CwpNoEndStatesError",
    "CwpUnsupportedElementError",
    "CwpNoParentEdgeError",
    "CwpNoStartStateError",
    "CwpInvalidLiteralError",
    "CwpInvalidStartEdgeError",
    "CwpInvalidStartExpressionError",
    "CwpInvalidAssignmentError",
    "CwpInvalidAssignmentTargetError",
    "ExpressionComputationCompatabilityError",
    "ExpressionNegatorError",
    "ExpressionParseError",
    "StartExpressionDisallowedAssignemntError",
    "ExpressionRelationCompatabilityError",
    "ExpressionRelationalNotError",
    "ExpressionIfBranchCompatabilityError",
    "ExpressionIfConditionError",
    "ExpressionUnrecognizedID",
    "ExpressionOutOfScope",
    "ExpressionTripleInputError",
    "FileReadFileError",
    "FileWriteFileError",
    "FileXmlParseError",
    "FlowExpressionError",
    "MessageError",
    "NotImplementedError",
    "NotInitializedError",
    "SpinAssertionError",
    "SpinCoverageError",
    "SpinInvalidEndStateError",
    "SpinSyntaxError",
    "StateAntlrWalkerError",
    "StateArraySizeMissmatchError",
    "StateArraySizeZeroError",
    "StateInitNotInValues",
    "StateInitNotInValuesLineCol",
    "StateMultipleDefinitionError",
    "StateMultipleDefinitionErrorLineCol",
    "StateMultipleDefinitionErrorLineColPrevLinePrevCol",
    "StateSyntaxError",
    "SubprocessRunError",
    "TypeingAssignCompatabilityError",
    "TypingListCompatibiltiyError",
    "TypingListOfExpressionsError",
    "TypingTripleVariableError",
    "TypingNoTypeError",
    "CbmcAssertionError",
    "CbmcReachabilityError",
    "CbmcSubProcessError",
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


def test_constructor_and_get_counter_example():
    cee = CounterExampleError("test_counter_example")

    assert cee.counter_example == "test_counter_example"

    assert cee.get_counter_example() == "test_counter_example"
