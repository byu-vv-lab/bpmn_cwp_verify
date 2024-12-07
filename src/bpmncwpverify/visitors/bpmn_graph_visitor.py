import graphviz
from bpmncwpverify.core.bpmn import (
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    SubProcess,
    SequenceFlow,
    MessageFlow,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    BpmnVisitor,
    Bpmn,
)


class GraphVizVisitor(BpmnVisitor):  # type: ignore
    def __init__(self, process_number: int) -> None:
        self.dot = graphviz.Digraph(comment="Process graph {}".format(process_number))

    def visit_start_event(self, event: StartEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        self.dot.node(event.id, event.name)
        return True

    def visit_task(self, task: Task) -> bool:
        self.dot.node(task.id, task.name)
        return True

    def visit_sub_process(self, subprocess: SubProcess) -> bool:
        self.dot.node(subprocess.id, subprocess.name)
        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        self.dot.node(gateway.id, gateway.name)
        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        self.dot.node(gateway.id, gateway.name)
        return True

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        self.dot.edge(flow.source_node.id, flow.target_node.id, label=flow.name)

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        self.dot.edge(flow.source_node.id, flow.target_node.id, label=flow.name)

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        for msg_id, msg_flow in bpmn.inter_process_msgs.items():
            self.dot.edge(
                msg_flow.source_node.id, msg_flow.target_node.id, label="message_flow"
            )
