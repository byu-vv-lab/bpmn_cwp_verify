from bpmncwpverify.core.feel_tree import (
    BoolLiteralNode,
    ChooseNode,
    FeelVisitor,
    IfNode,
    ListNode,
    NumberLiteralNode,
    QualifiedNameNode,
    TripleNode,
)
from bpmncwpverify.util.stringmanager import NL_SINGLE, IndentAction, StringManager


class FeelToPromelaVisitor(FeelVisitor):
    __slots__ = ["promela", "target"]

    def __init__(self) -> None:
        self.promela = StringManager()

    def end_visit_number_literal(self, node: NumberLiteralNode) -> None:
        pass

    def end_visit_bool_literal(self, node: BoolLiteralNode) -> None:
        pass

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        self.promela.write_str(node.name)

    def visit_list(self, node: ListNode) -> bool:
        return True

    def visit_if(self, node: IfNode) -> bool:
        self.promela.write_str("if", NL_SINGLE)
        self.promela.write_str(":: ")

        return False

    def visit_choose(self, node: ChooseNode) -> bool:
        self.promela.write_str("if", NL_SINGLE, IndentAction.INC)

        for item in node.choices.values:
            self.promela.write_str(":: True -> ")
            item.accept(self)
            self.promela.write_str("= ")

        return True

    def visit_triple(self, node: TripleNode) -> bool:
        return True
