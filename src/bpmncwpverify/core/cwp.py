import html
import re
from typing import cast
from xml.etree.ElementTree import Element

from bs4 import BeautifulSoup
from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Failure, Result, Success

from bpmncwpverify.core.error import (
    CwpInvalidAssignmentError,
    CwpInvalidAssignmentTargetError,
    CwpInvalidLiteralError,
    CwpInvalidStartEdgeError,
    Error,
)
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.feel_tree import (
    AndNode,
    BoolLiteralNode,
    EqualNode,
    ExpressionNode,
    ListNode,
    NumberLiteralNode,
    QualifiedNameNode,
)


class Cwp:
    __slots__ = ["states", "edges", "start_state", "end_states"]

    def __init__(self) -> None:
        self.states: dict[str, CwpState] = {}
        self.edges: dict[str, CwpEdge] = {}
        self.start_state: CwpState
        self.end_states: list[CwpState] = []

    def accept(self, visitor: "CwpVisitor") -> None:
        result = visitor.visit_cwp(self)
        if result:
            self.start_state.accept(visitor)
        visitor.end_visit_cwp(self)


class CwpState:
    __slots__ = ["id", "name", "out_edges", "in_edges", "init_state"]

    def __init__(self, id: str, name: str) -> None:
        self.id = id
        self.name = name
        self.out_edges: list[CwpEdge] = []
        self.in_edges: list[CwpEdge] = []
        self.init_state: bool = False

    def accept(self, visitor: "CwpVisitor") -> None:
        result = visitor.visit_state(self)
        if result:
            for edge in self.out_edges:
                edge.accept(visitor)
        visitor.end_visit_state(self)

    @staticmethod
    def _clean_name(name: str) -> str:
        name = re.sub("[?,+=/]", "", name)
        name = re.sub("-", " ", name)
        name = re.sub(r"\s+", "_", name)
        name = re.sub("</?div>", "", name).strip()
        return name

    @staticmethod
    def from_xml(element: Element) -> "CwpState":
        id = element.get("id")
        if id is None:
            raise Exception("id not in cwp state")

        name = element.get("value") or id
        return CwpState(id, CwpState._clean_name(name))

    @staticmethod
    def from_mmd(state_id: str, display_name: str) -> "CwpState":
        return CwpState(state_id, CwpState._clean_name(display_name))


class CwpEdge:
    __slots__ = ["id", "name", "expression", "parent_id", "source", "dest", "is_leaf"]

    def __init__(self, id: str, name: str) -> None:
        self.id = id
        self.name = name
        self.expression: Feel
        self.parent_id: str

        self.source: CwpState | None = None
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

    def _literal_text(self, node: ExpressionNode) -> Result[str, Error]:
        if isinstance(node, NumberLiteralNode | BoolLiteralNode):
            return Success(node.value)
        if isinstance(node, QualifiedNameNode):
            return Success(node.name)
        return Failure(CwpInvalidLiteralError())

    def _flatten_and_equals(
        self, node: ExpressionNode
    ) -> Result[list[EqualNode], Error]:
        if isinstance(node, EqualNode):
            return Success([node])
        if isinstance(node, AndNode):
            left_result = self._flatten_and_equals(node.left)
            if not_(is_successful)(left_result):
                return left_result
            right_result = self._flatten_and_equals(node.right)
            if not_(is_successful)(right_result):
                return right_result
            return Success(left_result.unwrap() + right_result.unwrap())
        return Failure(CwpInvalidAssignmentError())

    def parse_initial_values(
        self,
    ) -> Result[list[tuple[str, str | list[str]]], Error]:
        if self.source or not self.expression:
            return Failure(CwpInvalidStartEdgeError())

        ast = self.expression.ast

        if isinstance(ast, ListNode):
            assignments_result: Result[list[EqualNode], Error] = Success([])
            for item in ast.values:
                item_result = self._flatten_and_equals(item)
                if not_(is_successful)(item_result):
                    return cast(
                        Result[list[tuple[str, str | list[str]]], Error], item_result
                    )
                assignments_result = Success(
                    assignments_result.unwrap() + item_result.unwrap()
                )
        else:
            assignments_result = self._flatten_and_equals(ast)
            if not_(is_successful)(assignments_result):
                return cast(
                    Result[list[tuple[str, str | list[str]]], Error], assignments_result
                )

        initial_values: list[tuple[str, str | list[str]]] = []

        for assignment in assignments_result.unwrap():
            if not isinstance(assignment.left, QualifiedNameNode):
                return Failure(CwpInvalidAssignmentTargetError())

            name = assignment.left.name

            if isinstance(assignment.right, ListNode):
                element_values: list[str] = []
                for element in assignment.right.values:
                    el_result = self._literal_text(element)
                    if not is_successful(el_result):
                        return cast(
                            Result[list[tuple[str, str | list[str]]], Error], el_result
                        )
                    element_values.append(el_result.unwrap())
                initial_values.append((name, element_values))
            else:
                value_result = self._literal_text(assignment.right)
                if not is_successful(value_result):
                    return cast(
                        Result[list[tuple[str, str | list[str]]], Error], value_result
                    )
                initial_values.append((name, value_result.unwrap()))

        return Success(initial_values)

    @staticmethod
    def has_html(expr: str) -> bool:
        HTML_HINTS = ("<br", "<span", "<div", "<font", "</")
        HTML_TAG_RE = re.compile(r"<\s*/?\s*[a-zA-Z][a-zA-Z0-9]*\b[^>]*>")

        if any(h in expr for h in HTML_HINTS):
            return True

        return bool(HTML_TAG_RE.search(expr))

    @staticmethod
    def deep_decode(expr: str) -> str:
        prev = expr

        for _ in range(5):
            curr = html.unescape(prev)

            if curr == prev:
                break
            prev = curr

        return prev

    @staticmethod
    def expression_reconstructor(s: list[str]) -> str:
        OPS = ("&&", "||")
        CONDITIONALS = ("==", "!=", "<=", "=<", "<", ">", ">=", "=>")
        ALL = OPS + CONDITIONALS
        prev_operation = ""
        i = 1

        while i != len(s):
            if i == len(s) - 1:
                break
            elif s[i] in OPS:
                prev_operation = s[i]
            elif s[i - 1] not in ALL and s[i] not in ALL:
                s.insert(i, prev_operation)
                i += 1
            i += 1

        return " ".join(s)

    @staticmethod
    def cleanup_expression(expression: str) -> str:
        decoded = CwpEdge.deep_decode(expression)
        decoded = re.sub(
            r"\s*(&&|\|\|)\s*", r" \1 ", decoded
        )  # adds spaces around logical operators for BeautifulSoup and expression_reconstructor

        if CwpEdge.has_html(decoded):
            soup = BeautifulSoup(decoded, "html.parser").get_text(" ", strip=True)
            decoded = CwpEdge.expression_reconstructor(soup.split())

        decoded = re.sub(
            r"\s*(&&|\|\||==|!=|>=|<=|=|<|>)\s*", r" \1 ", decoded
        )  # adds spaces between everything for standardization
        decoded = re.sub(
            r"\s+", " ", decoded
        ).strip()  # strips all extra spaces and leading/ending whitespace if any

        return decoded

    @staticmethod
    def build_ast(expression: str) -> Feel:
        return Feel.parse(expression)

    @staticmethod
    def from_xml(element: Element, name: str) -> "CwpEdge":
        id = element.get("id")
        if id is None:
            raise Exception("No ID for edge or no targetRef")
        return CwpEdge(id, name)

    @staticmethod
    def from_mmd(target_id: str, name: str) -> "CwpEdge":
        return CwpEdge(target_id, name)


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
