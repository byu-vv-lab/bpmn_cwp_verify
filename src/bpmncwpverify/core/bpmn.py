from bpmncwpverify.core.error import (
    BpmnStructureError,
)

from typing import List, Dict, Union, Generic, TypeVar, Type
from xml.etree.ElementTree import Element


BPMN_XML_NAMESPACE = {"bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL"}


T = TypeVar("T", bound="BpmnElement")


class BpmnElement(Generic[T]):
    """
    Parent class for all BPMN elements
    """

    __slots__ = ["element", "name", "id"]

    def __init__(self, element: Element) -> None:
        """
        Initialize BpmnElement object

        Args:
            element (Element): The element to store
        """
        self.element = element
        id = element.attrib.get("id")
        if not id:
            raise Exception("Id cannot be None")

        self.id = id

        self.name: str = element.attrib.get("name", self.id)

    @classmethod
    def from_xml(cls: Type[T], element: Element) -> T:
        return cls(element)


class Node(BpmnElement[T]):
    """
    Parent class for BPMN elements that have incoming and outgoing flows
    """

    __slots__ = [
        "out_flows",
        "in_flows",
        "in_msgs",
        "out_msgs",
        "message_event_definition",
        "message_timer_definition",
    ]

    def __init__(self, element: Element) -> None:
        """
        Initialize Node object
        """
        super().__init__(element)

        # Determine if node is a message type or timer type
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
        """
        Add an outgoing flow to the node

        Args:
            flow (SequenceFlow): Outgoing flow to add
        """
        self.out_flows.append(flow)

    def add_in_flow(self, flow: "SequenceFlow") -> None:
        """
        Add an incoming flow to the node

        Args:
            flow (SequenceFlow): Incoming flow to add
        """
        self.in_flows.append(flow)

    def add_out_msg(self, flow: "MessageFlow") -> None:
        """
        Add an outgoing message to the node

        Args:
            flow (MessageFlow): Outgoing message to add
        """
        self.out_msgs.append(flow)

    def add_in_msg(self, flow: "MessageFlow") -> None:
        """
        Add an incoming message to the node

        Args:
            flow (MessageFlow): Incoming message to add
        """
        self.in_msgs.append(flow)

    def traverse_outflows_if_result(self, visitor: "BpmnVisitor", result: bool) -> None:
        """
        Allow the visitor to go through outgoing flows if the result is true

        Args:
            visitor (BpmnVisitor): Visitor that will traverse the BPMN elements
            result (bool): Conditional that will tell us to traverse or not
        """
        if result:
            for flow in self.out_flows:
                flow.accept(visitor)

    def accept(self, visitor: "BpmnVisitor") -> None:
        """
        Accept the visitor to traverse through

        Args:
            visitor (BpmnVisitor): Visitor that will traverse through BPMN elements
        """
        pass


# Event classes
class Event(Node[T]):
    """
    Parent class for all BPMN events
    """

    pass


class StartEvent(Event["StartEvent"]):
    """
    Event that BPMN starts with
    """

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_start_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_start_event(self)


class EndEvent(Event["EndEvent"]):
    """
    Event that BPMN starts with
    """

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_end_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_end_event(self)


class IntermediateEvent(Event["IntermediateEvent"]):
    """
    Events between start and end events
    """

    def __init__(self, element: Element):
        """
        Initialize IntermediateEvent object
        """
        super().__init__(element)
        tag = element.tag.partition("}")[2]
        self.type = "catch" if "Catch" in tag else "throw" if "Throw" in tag else "send"

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_intermediate_event(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_intermediate_event(self)


# Activity classes
class Task(Node["Task"]):
    """
    Action that can be acted upon varaible(s)
    """

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_task(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_task(self)


# Gateway classes
class GatewayNode(Node[T]):
    """
    Parent class for all BPMN gateways
    """

    pass


class ExclusiveGatewayNode(GatewayNode["ExclusiveGatewayNode"]):
    """
    Gateway that only allows one path to be taken
    """

    def accept(self, visitor: "BpmnVisitor") -> None:
        result = visitor.visit_exclusive_gateway(self)
        self.traverse_outflows_if_result(visitor, result)
        visitor.end_visit_exclusive_gateway(self)


class ParallelGatewayNode(GatewayNode["ParallelGatewayNode"]):
    """
    Gateway that allows multiple paths to be taken
    """

    def __init__(self, element: Element, is_fork: bool = False):
        """
        Initialize ParallelGatewayNode object

        Args:
            is_fork (bool, optional): Variable determining if gateway is a forking gateway or not. Defaults to false.
        """
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


# Flow classes
class Flow(BpmnElement[T]):
    """
    Parent class for all BPMN flows
    """

    __slots__ = ["source_node", "target_node", "is_leaf"]

    def __init__(
        self,
        element: Element,
    ) -> None:
        """
        Initialize Flow object
        """
        super().__init__(element)
        self.source_node: Node
        self.target_node: Node
        self.is_leaf: bool = False


class SequenceFlow(Flow["SequenceFlow"]):
    """
    Representation of how activities and events are connected
    """

    __slots__ = ["expression"]

    def __init__(self, element: Element):
        """
        Initialize SequenceFlow object
        """
        super().__init__(element)
        self.expression: str = ""

    def accept(self, visitor: "BpmnVisitor") -> None:
        if visitor.visit_sequence_flow(self) and not self.is_leaf:
            self.target_node.accept(visitor)
        visitor.end_visit_sequence_flow(self)


class MessageFlow(Flow["MessageFlow"]):
    """
    Representation of how things are communicated between participants
    """


class Process(BpmnElement["Process"]):
    """
    Representation of the business process being modeled
    """

    def __init__(self, element: Element):
        """
        Initialize Process object
        """
        super().__init__(element)
        self._flows: Dict[str, SequenceFlow] = {}
        self._elements: Dict[str, Node] = {}
        self._start_states: Dict[str, StartEvent] = {}

    def __setitem__(self, key: str, item: BpmnElement) -> None:
        """
        Add item to the business process

        Args:
            key (str): String identifier of the item
            item (BpmnElement): Actual item to add to one of three dictionaries
        """
        if isinstance(item, StartEvent):
            self._start_states[key] = item
        elif isinstance(item, SequenceFlow):
            self._flows[key] = item
        elif isinstance(item, Node):
            self._elements[key] = item

    def __getitem__(self, key: str) -> Union[Node, Flow]:
        """
        Retrieve item stored in business process

        Args:
            key (str): String identifier of item
        """
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
        """
        Return flows of business model
        """
        return self._flows

    def all_items(self) -> Dict[str, Node]:
        """
        Return all items of business model
        """
        return self._elements | self._start_states

    def get_start_states(self) -> Dict[str, StartEvent]:
        """
        Return start states of business model
        """
        return self._start_states

    def accept(self, visitor: "BpmnVisitor") -> None:
        visitor.visit_process(self)
        for start_event in self.get_start_states().values():
            start_event.accept(visitor)
        visitor.end_visit_process(self)


def get_element_type(tag: str) -> Union[type[SequenceFlow], type[Node]]:
    """
    Maps tag name to its respective builder function

    Args:
        tag (str): String representation of builder function
    """
    mapping: Dict[str, Union[type[SequenceFlow], type[Node]]] = {
        "task": Task,
        "startEvent": StartEvent,
        "endEvent": EndEvent,
        "exclusiveGateway": ExclusiveGatewayNode,
        "parallelGateway": ParallelGatewayNode,
        "sendTask": IntermediateEvent,
        "intermediateCatchEvent": IntermediateEvent,
        "intermediateThrowEvent": IntermediateEvent,
        "sequenceFlow": SequenceFlow,
    }

    result = mapping.get(tag) or (
        mapping.get("task") if "task" in tag.lower() else None
    )

    assert result

    return result


class Bpmn:
    """
    BPMN Promela/graph constructor
    """

    def __init__(self) -> None:
        """
        Initialize Bpmn object
        """
        self.processes: Dict[str, Process] = {}
        self.id_to_element: Dict[str, BpmnElement] = {}  # Maps ids to elements
        self.inter_process_msgs: Dict[str, MessageFlow] = {}

    def store_element(self, element: BpmnElement) -> None:
        """
        Add an element to the BPMN graph

        Args:
            element (BpmnElement): Element to add
        """
        self.id_to_element[element.id] = element

    def get_element_from_id_mapping(self, key: str) -> BpmnElement:
        """
        Retrieve element by key

        Args:
            key (str): String representation of element
        """
        return self.id_to_element[key]

    def add_inter_process_msg(self, msg: MessageFlow) -> None:
        """
        Add an interprocess message to BPMN graph

        Args:
            msg (MessageFlow): Message to add
        """
        self.inter_process_msgs[msg.id] = msg

    def accept(self, visitor: "BpmnVisitor") -> None:
        """
        Accept the visitor to traverse through

        Args:
            visitor (BpmnVisitor): Visitor that will traverse through BPMN elements
        """
        visitor.visit_bpmn(self)
        for process in self.processes.values():
            process.accept(visitor)
        visitor.end_visit_bpmn(self)


class BpmnVisitor:
    """
    Visitor methods for when visitor is passing through elements of BPMN file
    """

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
