from xml.etree.ElementTree import Element

from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Failure, Result, Success

from bpmncwpverify.builder.process_builder import ProcessBuilder
from bpmncwpverify.core.bpmn import (
    BPMN_XML_NAMESPACE,
    Node,
    Process,
    SequenceFlow,
    Task,
    get_element_type,
)
from bpmncwpverify.core.error import Error
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.state import State


def get_process_name(id: str, parts: list[Element]) -> str:
    for part in parts:
        if id == part.attrib.get("processRef"):
            return part.attrib.get("name", id)

    return id


def parse_and_typecheck_optional_feel(
    text: str | None, state: State
) -> Result[Feel | None, Error]:
    if not text:
        return Success(None)  # nothing to do

    feel = Feel.parse(text)
    type_result = feel.type_check(state)
    if not is_successful(type_result):
        return Failure(type_result.failure())

    return Success(feel)


def from_xml(
    element: Element, participants: list[Element], state: State
) -> Result["Process", Error]:
    id = element.attrib.get("id")
    if not id:
        raise Exception("Id cannot be None")

    name: str = get_process_name(id, participants)

    builder = ProcessBuilder(id, name, state)

    for sub_element in element:
        tag = sub_element.tag.partition("}")[2]

        element_result = get_element_type(tag)
        if not_(is_successful)(element_result):
            return Failure(element_result.failure())
        element_type: type[SequenceFlow] | type[Node] = element_result.unwrap()

        class_object = element_type.from_xml(sub_element)

        # expression
        feel_result = parse_and_typecheck_optional_feel(
            getattr(class_object, "expression", None), state
        )
        if not is_successful(feel_result):
            return Failure(feel_result.failure())

        parsed = feel_result.unwrap()
        if parsed and isinstance(class_object, SequenceFlow):
            class_object.expression = parsed

        # behavior
        feel_result = parse_and_typecheck_optional_feel(
            getattr(class_object, "behavior", None), state
        )
        if not is_successful(feel_result):
            return Failure(feel_result.failure())

        parsed = feel_result.unwrap()
        if parsed and isinstance(class_object, Task):
            class_object.behavior = parsed

        # mainly to check if the Start Event is supported
        verified_result = class_object.verify_element(sub_element, class_object.id)
        if not_(is_successful)(verified_result):
            return Failure(verified_result.failure())

        builder = builder.with_element(class_object)

    for seq_flow in element.findall("bpmn:sequenceFlow", BPMN_XML_NAMESPACE):
        result_builder: Result[ProcessBuilder, Error] = builder.with_process_flow(
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

    return builder.build()
