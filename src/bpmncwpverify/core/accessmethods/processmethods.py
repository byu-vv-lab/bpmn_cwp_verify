from xml.etree.ElementTree import Element
from typing import Union
from bpmncwpverify.core.state import State
from returns.result import Result, Failure
from bpmncwpverify.core.error import Error
from bpmncwpverify.builder.process_builder import ProcessBuilder
from bpmncwpverify.core.bpmn import (
    Process,
    get_element_type,
    BPMN_XML_NAMESPACE,
    SequenceFlow,
    Node,
)
from returns.pipeline import is_successful
from returns.functions import not_


def from_xml(element: Element, state: State) -> Result["Process", Error]:
    id = element.attrib.get("id")
    if not id:
        raise Exception("Id cannot be None")
    name: str = element.attrib.get("name", id)
    builder = ProcessBuilder(id, name, state)

    for sub_element in element:
        tag = sub_element.tag.partition("}")[2]

        result = get_element_type(tag)
        if not_(is_successful)(result):
            return Failure(result.failure())
        element_type: Union[type[SequenceFlow], type[Node]] = result.unwrap()

        class_object = element_type.from_xml(sub_element)
        builder = builder.with_element(class_object)

    for seq_flow in element.findall("bpmn:sequenceFlow", BPMN_XML_NAMESPACE):
        result_builder: Result["ProcessBuilder", Error] = builder.with_process_flow(
            seq_flow.attrib["id"],
            seq_flow.attrib["sourceRef"],
            seq_flow.attrib["targetRef"],
            seq_flow.attrib.get("name", ""),
        )
        if is_successful(result_builder):
            builder = result_builder.unwrap()
        else:
            return Failure(result_builder.failure())

    builder = builder.with_boundary_events()

    builder = builder.with_boundary_events()

    return builder.build()
