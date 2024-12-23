from __future__ import annotations
from bpmncwpverify.core.bpmn import (
    BpmnElement,
    Process,
    Bpmn,
)
from bpmncwpverify.core.error import (
    BpmnStructureError,
)
from returns.result import Result, Failure, Success
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidate import validate_process


class ProcessBuilder:
    def __init__(self, bpmn: Bpmn, process: Process) -> None:
        self._process = process
        self._bpmn = bpmn

    def with_element(self, element: BpmnElement) -> None:
        self._process[element.id] = element
        self._bpmn.store_element(element)

    def build(self) -> Result[Process, BpmnStructureError]:
        try:
            self._bpmn.processes[self._process.id] = self._process

            validate_process(self._process)
            return Success(self._process)
        except Exception as e:
            return Failure(e.args[0])
