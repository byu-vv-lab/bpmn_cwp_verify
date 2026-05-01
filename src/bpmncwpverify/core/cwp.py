import html
import re
from xml.etree.ElementTree import Element

from bs4 import BeautifulSoup


class Cwp:
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
    def __init__(self, id: str, name: str) -> None:
        self.id = id
        self.name = name
        self.out_edges: list[CwpEdge] = []
        self.in_edges: list[CwpEdge] = []

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
        self.expression: str = (
            ""  # TODO: expression needs to always be on an edge and cannot be empty
        )
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
    def conditional_folier(s: list[str]) -> str:
        OPS = ("&&", "||")
        CONDITIONALS = ("==", "!=", "<=", "=<", "<", ">", ">=", "=>")
        ALL = OPS + CONDITIONALS
        prev_operation = ""
        i = 0

        while i != len(s):
            if i == len(s) - 1:
                break
            elif s[i] in OPS:
                prev_operation = s[i]
            elif s[i] not in ALL and s[i + 1] not in ALL:
                s.insert(i + 1, prev_operation)
            i += 1

        return " ".join(s)

    @staticmethod
    def cleanup_expression(expression: str) -> str:
        decoded = CwpEdge.deep_decode(expression)
        decoded = re.sub(r"\s*(&&|\|\|)\s*", r" \1 ", decoded)

        if CwpEdge.has_html(decoded):
            soup = BeautifulSoup(decoded, "html.parser").get_text(" ", strip=True)
            decoded = CwpEdge.conditional_folier(soup.split())

        decoded = re.sub(r"\s*(&&|\|\||==|!=|>=|<=|=|<|>)\s*", r" \1 ", decoded)
        decoded = re.sub(r"\s+", " ", decoded).strip()

        return decoded

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
