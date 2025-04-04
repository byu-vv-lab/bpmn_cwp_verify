from typing import cast
from xml.etree.ElementTree import Element
from bpmncwpverify.core.state import State
from returns.result import Result, Failure
from bpmncwpverify.core.error import Error
from bpmncwpverify.builder.process_builder import ProcessBuilder
from bpmncwpverify.core.bpmn import Process, get_element_type, BPMN_XML_NAMESPACE
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
        result = result.unwrap()

        class_object = result.from_xml(sub_element)
        builder = builder.with_element(class_object)

    for seq_flow in element.findall("bpmn:sequenceFlow", BPMN_XML_NAMESPACE):
        result = builder.with_process_flow(
            seq_flow.attrib["id"],
            seq_flow.attrib["sourceRef"],
            seq_flow.attrib["targetRef"],
            seq_flow.attrib.get("name", ""),
        )
        if is_successful(result):
            builder = result.unwrap()
        else:
            return Failure(result.failure())

    return cast(Result[Process, Error], builder.build())
