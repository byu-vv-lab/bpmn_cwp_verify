from bpmncwpverify.core.bpmn import Bpmn, Process
from bpmncwpverify.core.error import BpmnMsgFlowSamePoolError, Error
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidations import (
    validate_start_end_events,
)
from bpmncwpverify.visitors.bpmnchecks.checkmethods import (
    check_connectivity,
    set_leaf_flows,
    validate_bpmn_incoming_flows,
    validate_bpmn_outgoing_flows,
    validate_start_event_flows,
    validate_bpmn_ids,
    validate_msgs,
    validate_seq_flows,
)
from returns.result import Result, Failure, Success
from returns.pipeline import flow
from returns.pointfree import bind_result


def validate_bpmn(bpmn: Bpmn) -> Result[Bpmn, Error]:
    for msg in bpmn.inter_process_msgs.values():
        for process in bpmn.processes.values():
            if (
                msg.target_node.id in process.all_items()
                and msg.source_node.id in process.all_items()
            ):
                return Failure(BpmnMsgFlowSamePoolError(msg.id))
    return Success(bpmn)


def validate_process(process: Process) -> Result[Process, Error]:
    result: Result[Process, Error] = flow(
        process,
        validate_start_end_events,
        bind_result(set_leaf_flows),
        bind_result(check_connectivity),
        bind_result(validate_msgs),
        bind_result(validate_seq_flows),
        bind_result(validate_bpmn_incoming_flows),
        bind_result(validate_bpmn_outgoing_flows),
        bind_result(validate_start_event_flows),
        bind_result(validate_bpmn_ids),
    )
    return result
