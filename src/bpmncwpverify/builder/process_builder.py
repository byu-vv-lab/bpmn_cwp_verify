from bpmncwpverify.core.bpmn import Node, Process, SequenceFlow
from bpmncwpverify.core.expr import ExpressionListener
from bpmncwpverify.core.error import BpmnStructureError
from bpmncwpverify.core.state import State
from bpmncwpverify.visitors.bpmnchecks.bpmnvalidate import validate_process

from returns.result import Result
from returns.pipeline import is_successful
from returns.functions import not_

from typing import Union, cast


class ProcessBuilder:
    __slots__ = ["_process", "_symbol_table"]

    def __init__(self, id: str, name: str, symbol_table: State) -> None:
        self._process = Process(id, name)
        self._symbol_table = symbol_table

    def with_element(self, element: Union[SequenceFlow, Node]) -> "ProcessBuilder":
        self._process[element.id] = element
        return self

    def with_process_flow(
        self,
        flow_id: str,
        source_ref: str,
        target_ref: str,
        expression: Union[str, None],
    ) -> "ProcessBuilder":
        flow = self._process[flow_id]
        source_node = self._process[source_ref]
        target_node = self._process[target_ref]

        assert isinstance(flow, SequenceFlow)
        assert isinstance(source_node, Node)
        assert isinstance(target_node, Node)

        if expression:
            result = ExpressionListener.type_check(expression, self._symbol_table)
            if not_(is_successful)(result) or result.unwrap() != "bool":
                raise Exception(result.failure())
            flow.expression = expression

        flow.source_node = source_node
        flow.target_node = target_node

        source_node.add_out_flow(flow)
        target_node.add_in_flow(flow)
        return self

    def build(self) -> Result[Process, BpmnStructureError]:
        return cast(Result, validate_process(self._process))
