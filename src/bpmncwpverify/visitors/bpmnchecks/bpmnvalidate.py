from bpmncwpverify.core.bpmn import Bpmn, Process


def validate_bpmn(bpmn: Bpmn) -> None:
    from bpmncwpverify.visitors.bpmnchecks.bpmn_connectivity_visitor import (
        BpmnConnectivityVisitor,
    )

    visitor = BpmnConnectivityVisitor()

    bpmn.accept(visitor)


def validate_process(process: Process) -> None:
    from bpmncwpverify.visitors.bpmnchecks.setflowleafs import SetFlowLeafs
    from bpmncwpverify.visitors.bpmnchecks.process_connectivity_visitor import (
        ProcessConnectivityVisitor,
    )

    set_leafs_visitor = SetFlowLeafs()
    process_connectivity_visitor = ProcessConnectivityVisitor()

    process.accept(set_leafs_visitor)
    process.accept(process_connectivity_visitor)
