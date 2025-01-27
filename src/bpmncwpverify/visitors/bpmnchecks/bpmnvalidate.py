from bpmncwpverify.core.bpmn import Bpmn, Process
from bpmncwpverify.core.error import BpmnMsgFlowSamePoolError, Error
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidations import (
    ValidateBpmnIncomingFlows,
    ValidateBpmnOutgoingFlows,
    ValidateMsgsVisitor,
    ValidateSeqFlowVisitor,
    ValidateStartEventFlows,
    ProcessConnectivityVisitor,
    SetFlowLeafs,
    validate_start_end_events,
)
from returns.result import Result, Success


def validate_bpmn(bpmn: Bpmn) -> None:
    def msg_connects_diff_pools() -> None:
        for msg in bpmn.inter_process_msgs.values():
            for process in bpmn.processes.values():
                if (
                    msg.target_node.id in process.all_items()
                    and msg.source_node.id in process.all_items()
                ):
                    raise Exception(BpmnMsgFlowSamePoolError(msg.id))

    msg_connects_diff_pools()


# process is going to have a static method for each of the accepts (i.e. set_leafs_vistitor)
# in this method I create the visitor and call try catch and return a Result[Process, Error]


def validate_process(process: Process) -> Result[bool, Error]:
    set_leafs_visitor = SetFlowLeafs()
    process_connectivity_visitor = ProcessConnectivityVisitor()
    validate_msgs_visitor = ValidateMsgsVisitor()
    validate_seq_flow_visitor = ValidateSeqFlowVisitor()
    validate_bpmn_incoming_flows = ValidateBpmnIncomingFlows()
    validate_bpmn_outgoing_flows = ValidateBpmnOutgoingFlows()
    validate_start_event_flows = ValidateStartEventFlows()

    # this should all go in a flow (no try catch here)
    validate_start_end_events(process)
    process.accept(set_leafs_visitor)
    process.accept(process_connectivity_visitor)
    process.accept(validate_msgs_visitor)
    process.accept(validate_seq_flow_visitor)
    process.accept(validate_bpmn_incoming_flows)
    process.accept(validate_bpmn_outgoing_flows)
    process.accept(validate_start_event_flows)

    return Success(True)
