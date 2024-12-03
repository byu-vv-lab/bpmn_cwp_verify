from xml.etree.ElementTree import Element, SubElement, tostring
from defusedxml import ElementTree
from bpmncwpverify.constants import NAMESPACES
from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.state import SymbolTable
from returns.result import Failure


def test_complete_bpmn_with_no_start_state_process():
    symbol_table = SymbolTable()

    root = Element(
        "bpmn:definitions",
        attrib={
            "xmlns:bpmn": NAMESPACES["bpmn"],
            "id": "Definitions_1",
            "targetNamespace": "http://example.com/schema/bpmn",
        },
    )

    collab = SubElement(root, "bpmn:collaboration", attrib={"id": "Collaboration_1"})
    SubElement(
        collab,
        "bpmn:participant",
        attrib={
            "id": "Participant_1",
            "name": "Test Participant",
            "processRef": "Process_1",
        },
    )

    process = SubElement(
        root, "bpmn:process", attrib={"id": "Process_1", "isExecutable": "false"}
    )
    SubElement(process, "bpmn:task", attrib={"id": "Task_1", "name": "Test Task"})

    bpmn = tostring(root, encoding="unicode")

    root = ElementTree.fromstring(bpmn)
    result = Bpmn.from_xml(root, symbol_table)
    assert isinstance(result, Failure)
    exception = result.failure()
    assert exception == "Error with end events or start events: # end events = 0, # start events = 0"
