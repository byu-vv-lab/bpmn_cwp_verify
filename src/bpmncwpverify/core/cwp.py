from typing import Dict, List, Optional
from xml.etree.ElementTree import Element
import re


class Cwp:
    def __init__(self) -> None:
        self.states: Dict[str, CwpState] = {}
        self.edges: Dict[str, CwpEdge] = {}
        self.start_state: CwpState
        self.end_states: List[CwpState] = []

    def accept(self, visitor: "CwpVisitor") -> None:
        result = visitor.visit_cwp(self)
        if result:
            self.start_state.accept(visitor)
        visitor.end_visit_cwp(self)


class CwpState:
    def __init__(self, id: str, name: str) -> None:
        self.id = id
        self.name = name
        self.out_edges: List[CwpEdge] = []
        self.in_edges: List[CwpEdge] = []

    def accept(self, visitor: "CwpVisitor") -> None:
        result = visitor.visit_state(self)
        if result:
            for edge in self.out_edges:
                edge.accept(visitor)
        visitor.end_visit_state(self)

    @staticmethod
    def from_xml(element: Element) -> "CwpState":
        id = element.get("id")
        name = element.get("value")
        if id is None:
            raise Exception("id not in cwp state")
        if name is None:
            name = id
        name = re.sub("[?,+=/]", "", name)
        name = re.sub("-", " ", name)
        name = re.sub(r"\s+", "_", name)
        name = re.sub("</?div>", "", name).strip()
        return CwpState(id, name)


class CwpEdge:
    def __init__(self, id: str, name: str) -> None:
        self.id = id
        self.name = name
        self.expression: str
        self.parent_id: str

        self.source: Optional[CwpState] = None
        self.dest: CwpState
        self.is_leaf = False

    def set_source(self, state: CwpState) -> None:
        self.source = state

    def set_dest(self, state: CwpState) -> None:
        self.dest = state

    def accept(self, visitor: "CwpVisitor") -> None:
        if visitor.visit_edge(self) and not self.is_leaf:
            self.dest.accept(visitor)
        visitor.end_visit_edge(self)

    @staticmethod
    def cleanup_expression(expression: str) -> str:
        expression = re.sub(r"&amp;amp;|&amp;", "&", expression)
        expression = re.sub(r"&lt;", "<", expression)
        expression = re.sub(r"&gt;", ">", expression)

        expression = re.sub(r"</?div>", "", expression)
        expression = re.sub(r"<br>", " ", expression)

        expression = re.sub(r"\s*(==|!=|&&|\|\|)\s*", r" \1 ", expression)

        expression = re.sub(r"\s+", " ", expression)

        return expression.strip()

    @staticmethod
    def from_xml(element: Element, name: str) -> "CwpEdge":
        id = element.get("id")
        if id is None:
            raise Exception("No ID for edge or no targetRef")
        return CwpEdge(id, name)


class CwpVisitor:
    def visit_state(self, state: CwpState) -> bool:
        return True

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> bool:
        return True

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass

    def visit_cwp(self, model: Cwp) -> bool:
        return True

    def end_visit_cwp(self, model: Cwp) -> None:
        pass
