from typing import List, Dict, Type, Union
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import State
from returns.result import Result, Failure
from returns.pipeline import is_successful
from returns.functions import not_
from abc import abstractmethod
from bpmncwpverify.core.error import (
    BpmnStructureError,
    Error,
)

BPMN_XML_NAMESPACE = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}


###################
# Base class for all BPMN elements
###################
class BpmnElement:
    __slots__ = ["element", "name", "id"]

    def __init__(self, element: Element) -> None:
        self.element = element
        id = element.attrib.get("id")
        if not id:
            raise Exception("Id cannot be None")

        self.id = id

        self.name: str = element.attrib.get("name", self.id)


###################
# Base class for nodes that can have incoming and outgoing flows
###################
class Node(BpmnElement):
    __slots__ = [
        "out_flows",
        "in_flows",
        "in_msgs",
        "out_msgs",
        "message_event_definition",
        "message_timer_definition",
    ]

    def __init__(self, element: Element) -> None:
        super().__init__(element)

        message_event_def = element.find(
            "bpmn:messageEventDefinition", BPMN_XML_NAMESPACE
        )
        self.message_event_definition: str = (
            message_event_def.attrib.get("id", "")
            if message_event_def is not None
            else ""
        )

        timer_event_def = element.find("bpmn:timerEventDefinition", BPMN_XML_NAMESPACE)
        self.message_timer_definition: str = (
            timer_event_def.attrib.get("id", "") if timer_event_def is not None else ""
        )

        self.out_flows: List[SequenceFlow] = []
        self.in_flows: List[SequenceFlow] = []
        self.in_msgs: List[MessageFlow] = []
        self.out_msgs: List[MessageFlow] = []

    def add_out_flow(self, flow: "SequenceFlow") -> None:
        self.out_flows.append(flow)

    def add_in_flow(self, flow: "SequenceFlow") -> None:
        self.in_flows.append(flow)

    def add_out_msg(self, flow: "MessageFlow") -> None:
        self.out_msgs.append(flow)

    def add_in_msg(self, flow: "MessageFlow") -> None:
        self.in_msgs.append(flow)

    def traverse_outflows_if_result(self, visitor: "BpmnVisitor", result: bool) -> None:
        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

    def accept(self, visitor: "BpmnVisitor") -> None:
        pass

    @staticmethod
    @abstractmethod
    def from_xml(bpmn: "Bpmn", process: "Process", element: Element) -> "Node":
        pass


###################
# Event classes
###################
class Event(Node):
    pass


class StartEvent(Event):
    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_start_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_start_event(self)

    @staticmethod
    def from_xml(bpmn: "Bpmn", process: "Process", element: Element) -> "StartEvent":
        element_instance = StartEvent(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


class EndEvent(Event):
    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_end_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_end_event(self)

    @staticmethod
    def from_xml(bpmn: "Bpmn", process: "Process", element: Element) -> "EndEvent":
        element_instance = EndEvent(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


class IntermediateEvent(Event):
    def __init__(self, element: Element):
        super().__init__(element)
        tag = element.tag.partition("}")[2]
        self.type = "catch" if "Catch" in tag else "throw" if "Throw" in tag else "send"

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_intermediate_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_intermediate_event(self)

    @staticmethod
    def from_xml(
        bpmn: "Bpmn", process: "Process", element: Element
    ) -> "IntermediateEvent":
        element_instance = IntermediateEvent(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


###################
# Activity classes
###################
class Task(Node):
    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_task(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_task(self)

    @staticmethod
    def from_xml(bpmn: "Bpmn", process: "Process", element: Element) -> "Task":
        element_instance = Task(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


###################
# Gateway classes
###################
class GatewayNode(Node):
    pass


class ExclusiveGatewayNode(GatewayNode):
    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_exclusive_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_exclusive_gateway(self)

    @staticmethod
    def from_xml(
        bpmn: "Bpmn", process: "Process", element: Element
    ) -> "ExclusiveGatewayNode":
        element_instance = ExclusiveGatewayNode(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


class ParallelGatewayNode(GatewayNode):
    def __init__(self, element: Element, is_fork: bool = False):
        super().__init__(element)
        self.is_fork = is_fork

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_parallel_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_parallel_gateway(self)

    def add_out_flow(self, flow: "SequenceFlow") -> None:
        super().add_out_flow(flow)
        if len(self.out_flows) > 1:
            self.is_fork = True

    @staticmethod
    def from_xml(
        bpmn: "Bpmn", process: "Process", element: Element
    ) -> "ParallelGatewayNode":
        element_instance = ParallelGatewayNode(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


###################
# Flow classes
###################
class Flow(BpmnElement):
    __slots__ = ["source_node", "target_node", "is_leaf"]

    def __init__(
        self,
        element: Element,
    ) -> None:
        super().__init__(element)
        self.source_node: Node
        self.target_node: Node
        self.is_leaf: bool = False

    @staticmethod
    @abstractmethod
    def from_xml(bpmn: "Bpmn", process: "Process", element: Element) -> "Flow":
        pass


class SequenceFlow(Flow):
    __slots__ = ["expression"]

    def __init__(self, element: Element):
        super().__init__(element)
        self.expression: str = ""

    def accept(self, visitor: "BpmnVisitor") -> None:
        if visitor.visit_sequence_flow(self) and not self.is_leaf:
            self.target_node.accept(visitor)
        visitor.end_visit_sequence_flow(self)

    @staticmethod
    def from_xml(bpmn: "Bpmn", process: "Process", element: Element) -> "SequenceFlow":
        element_instance = SequenceFlow(element)
        process[element_instance.id] = element_instance
        bpmn.store_element(element_instance)
        return element_instance


class MessageFlow(Flow):
    pass


###################
# Process class
###################
class Process(BpmnElement):
    def __init__(self, element: Element):
        super().__init__(element)
        self._flows: Dict[str, SequenceFlow] = {}
        self._elements: Dict[str, Node] = {}
        self._start_states: Dict[str, StartEvent] = {}

    def __setitem__(self, key: str, item: BpmnElement) -> None:
        if isinstance(item, StartEvent):
            self._start_states[key] = item
        elif isinstance(item, SequenceFlow):
            self._flows[key] = item
        elif isinstance(item, Node):
            self._elements[key] = item

    def __getitem__(self, key: str) -> Union[Node, Flow]:
        if key in self._elements:
            return self._elements[key]
        elif key in self._start_states:
            return self._start_states[key]
        elif key in self._flows:
            return self._flows[key]
        raise Exception(
            BpmnStructureError(key, "Key not found in any of the processe's elements")
        )

    def get_flows(self) -> Dict[str, SequenceFlow]:
        return self._flows

    def all_items(self) -> Dict[str, Node]:
        return self._elements | self._start_states

    def get_start_states(self) -> Dict[str, StartEvent]:
        return self._start_states

    @staticmethod
    def from_xml(bpmn: "Bpmn", process_element: Element) -> "Process":
        process = Process(process_element)
        for element in process_element:

            def get_tag_name(element: Element) -> str:
                return element.tag.partition("}")[2]

            tag_name = get_tag_name(element)
            element_class = Bpmn._TAG_CLASS_MAPPING.get(tag_name) or (
                Bpmn._TAG_CLASS_MAPPING["task"] if "task" in tag_name.lower() else None
            )
            flow_class = Bpmn._FLOW_MAPPING.get(tag_name)

            assert element_class or flow_class, "Element type unknown"

            if element_class:
                element_class.from_xml(bpmn, process, element)
            elif flow_class:
                flow_class.from_xml(bpmn, process, element)

        return process

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_process(self)
        for start_event in self.get_start_states().values():
            start_event.accept(visitor)
        visitor.end_visit_process(self)


###################
# Bpmn class (building graph from xml happens here)
###################
class Bpmn:
    _TAG_CLASS_MAPPING: Dict[str, Type[Node]] = {
        "task": Task,
        "startEvent": StartEvent,
        "endEvent": EndEvent,
        "exclusiveGateway": ExclusiveGatewayNode,
        "parallelGateway": ParallelGatewayNode,
        "sendTask": IntermediateEvent,
        "intermediateCatchEvent": IntermediateEvent,
        "intermediateThrowEvent": IntermediateEvent,
    }

    _FLOW_MAPPING = {"sequenceFlow": SequenceFlow}
    _MSG_MAPPING = {"messageFlow": MessageFlow}

    def __init__(self) -> None:
        self.processes: Dict[str, Process] = {}
        self.id_to_element: Dict[str, BpmnElement] = {}  # Maps ids to elements
        self.inter_process_msgs: Dict[str, MessageFlow] = {}

    def store_element(self, element: BpmnElement) -> None:
        self.id_to_element[element.id] = element

    def get_element_from_id_mapping(self, key: str) -> BpmnElement:
        return self.id_to_element[key]

    def add_inter_process_msg(self, msg: MessageFlow) -> None:
        self.inter_process_msgs[msg.id] = msg

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_bpmn(self)
        for process in self.processes.values():
            process.accept(visitor)
        visitor.end_visit_bpmn(self)

    def generate_graph_viz(self) -> None:
        from bpmncwpverify.visitors.bpmn_graph_visitor import GraphVizVisitor

        for process in range(len(self.processes)):
            graph_viz_visitor = GraphVizVisitor(process + 1)

            self.accept(graph_viz_visitor)

            graph_viz_visitor.dot.render("graphs/bpmn_graph.gv", format="png")  # type: ignore[unused-ignore]

    def generate_promela(self) -> str:
        from bpmncwpverify.visitors.bpmn_promela_visitor import PromelaGenVisitor

        promela_visitor = PromelaGenVisitor()

        self.accept(promela_visitor)

        return str(promela_visitor)

    @staticmethod
    def from_xml(root: Element, symbol_table: State) -> Result["Bpmn", Error]:
        from bpmncwpverify.builder.bpmn_builder import BpmnBuilder

        builder = BpmnBuilder()
        processes = root.findall("bpmn:process", BPMN_XML_NAMESPACE)
        result: Result["Bpmn", Error] = Failure(Error())
        process_result: Result[Process, Error] = Failure(Error())
        for process_element in processes:
            process_result = builder.with_process(process_element, symbol_table)
            if not_(is_successful)(process_result):
                return Failure(process_result.failure())

        collab = root.find("bpmn:collaboration", BPMN_XML_NAMESPACE)
        if collab is not None:
            for msg_flow in collab.findall("bpmn:messageFlow", BPMN_XML_NAMESPACE):
                builder.with_message(msg_flow)
        result = builder.build()
        return result


###################
# Bpmn Visitor interface
###################
class BpmnVisitor:
    def visit_start_event(self, event: StartEvent) -> bool:
        return True

    def end_visit_start_event(self, event: StartEvent) -> None:
        pass

    def visit_end_event(self, event: EndEvent) -> bool:
        return True

    def end_visit_end_event(self, event: EndEvent) -> None:
        pass

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        return True

    def end_visit_intermediate_event(self, event: IntermediateEvent) -> None:
        pass

    def visit_task(self, task: Task) -> bool:
        return True

    def end_visit_task(self, task: Task) -> None:
        pass

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        return True

    def end_visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> None:
        pass

    def visit_sequence_flow(self, flow: SequenceFlow) -> bool:
        return True

    def end_visit_sequence_flow(self, flow: SequenceFlow) -> None:
        pass

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return True

    def end_visit_message_flow(self, flow: MessageFlow) -> None:
        pass

    def visit_process(self, process: Process) -> bool:
        return True

    def end_visit_process(self, process: Process) -> None:
        pass

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        pass
