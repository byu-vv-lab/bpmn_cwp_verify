from bpmncwpverify.core.bpmn import Bpmn, Process
from bpmncwpverify.error import BpmnMsgFlowSamePoolError
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidations import (
    ValidateEndEventVisitor,
    ValidateGwOutflowVisitor,
    ValidateMsgsVisitor,
    ValidateTaskVisitor,
    validate_start_end_events,
)


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


def validate_process(process: Process) -> None:
    from bpmncwpverify.visitors.bpmnchecks.setflowleafs import SetFlowLeafs
    from bpmncwpverify.visitors.bpmnchecks.bpmnvalidations import (
        ProcessConnectivityVisitor,
    )

    set_leafs_visitor = SetFlowLeafs()
    process_connectivity_visitor = ProcessConnectivityVisitor()
    validate_task_visitor = ValidateTaskVisitor()
    validate_end_event_visitor = ValidateEndEventVisitor()
    validate_gw_out_flow_visitor = ValidateGwOutflowVisitor()
    validate_msgs_visitor = ValidateMsgsVisitor()

    validate_start_end_events(process)
    process.accept(set_leafs_visitor)
    process.accept(process_connectivity_visitor)
    process.accept(validate_task_visitor)
    process.accept(validate_end_event_visitor)
    process.accept(validate_gw_out_flow_visitor)
    process.accept(validate_msgs_visitor)
