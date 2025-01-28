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
    validate_msgs,
    validate_seq_flows,
)
from returns.result import Result
from returns.pipeline import flow
from returns.pointfree import bind_result


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
        bind_result(validate_bpmn_incoming_flows),
    )
    return result
