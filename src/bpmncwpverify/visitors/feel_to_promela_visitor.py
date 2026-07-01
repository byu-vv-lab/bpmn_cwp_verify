from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BinaryOperatorNode,
    BoolLiteralNode,
    ChooseNode,
    ComparisonOperatorNode,
    ConditionalOperatorNode,
    EqualNode,
    FeelVisitor,
    GENode,
    GTNode,
    IfNode,
    LENode,
    ListNode,
    LTNode,
    MultiplyNode,
    NotNode,
    NumberLiteralNode,
    OrNode,
    QualifiedNameNode,
    SubtractNode,
    TripleNode,
)
from bpmncwpverify.util.stringmanager import NL_SINGLE, StringManager


class FeelToPromelaVisitor(FeelVisitor):
    __slots__ = ["promela", "tripletarget", "triplechoose"]

    def __init__(self) -> None:
        self.promela = StringManager()
        self.tripletarget = ""
        self.triplechoose = StringManager()

    def visit_number_literal(self, node: NumberLiteralNode) -> bool:
        self.promela.write_str(node.value)
        return True

    def visit_bool_literal(self, node: BoolLiteralNode) -> bool:
        self.promela.write_str(node.value)
        return True

    def visit_qualified_name(self, node: QualifiedNameNode) -> bool:
        self.promela.write_str(node.name)
        return True

    def visit_list(self, node: ListNode) -> bool:
        self.promela.write_str("{")

        for item in node.values:
            item.accept(self)

            if node.values.index(item) != len(node.values) - 1:
                self.promela.write_str(", ")

        self.promela.write_str("}")
        return False

    def end_visit_list(self, node: ListNode) -> None:
        pass

    def visit_binary_operator(self, node: BinaryOperatorNode) -> bool:
        self.promela.write_str("(")
        node.left.accept(self)

        if isinstance(node, AddNode):
            self.promela.write_str(" + ")
        elif isinstance(node, SubtractNode):
            self.promela.write_str(" - ")
        elif isinstance(node, MultiplyNode):
            self.promela.write_str(" * ")
        else:
            self.promela.write_str(" / ")

        node.right.accept(self)
        self.promela.write_str(")")

        return False

    def end_visit_binary_operator(self, node: BinaryOperatorNode) -> None:
        pass

    def visit_comparision(self, node: ComparisonOperatorNode) -> bool:
        self.promela.write_str("(")
        node.left.accept(self)

        if isinstance(node, LTNode):
            self.promela.write_str(" < ")
        elif isinstance(node, GTNode):
            self.promela.write_str(" > ")
        elif isinstance(node, LENode):
            self.promela.write_str("<=")
        elif isinstance(node, GENode):
            self.promela.write_str(" >= ")
        elif isinstance(node, EqualNode):
            self.promela.write_str(" == ")
        else:
            self.promela.write_str(" != ")

        node.right.accept(self)
        self.promela.write_str(")")
        return False

    def visit_conditional(self, node: ConditionalOperatorNode) -> bool:
        self.promela.write_str("(")
        node.left.accept(self)

        if isinstance(node, AndNode):
            self.promela.write_str(" && ")
        elif isinstance(node, OrNode):
            self.promela.write_str(" || ")
        else:
            self.promela.write_str(" && ")
            self.promela.write_str("!")
            node.right.accept(self)
            self.promela.write_str(" || ")
            self.promela.write_str("!")
            node.left.accept(self)
            self.promela.write_str(" && ")

        node.right.accept(self)
        self.promela.write_str(")")
        return False

    def end_visit_conditional(self, node: ConditionalOperatorNode) -> None:
        pass

    def visit_not(self, node: NotNode) -> bool:
        self.promela.write_str("!")
        return True

    def end_visit_not(self, node: NotNode) -> None:
        pass

    def visit_if(self, node: IfNode) -> bool:
        self.promela.write_str("(")

        node.condition.accept(self)

        self.promela.write_str(" -> ")

        node.thendo.accept(self)

        self.promela.write_str(" : ")

        node.elsedo.accept(self)

        self.promela.write_str(")")

        return False

    def end_visit_if(self, node: IfNode) -> None:
        pass

    def visit_choose(self, node: ChooseNode) -> bool:
        name = self.tripletarget

        self.promela.write_str(f"choose_{name}[choose_{name}_i]")

        return False

    def end_visit_choose(self, node: ChooseNode) -> None:
        pass

    def visit_triple(self, node: TripleNode) -> bool:
        assert isinstance(node.target, QualifiedNameNode)
        self.tripletarget = node.target.name

        choose_visitor = FeelToPromelaChooseVisitor(
            self.tripletarget, self.triplechoose
        )
        node.value.accept(choose_visitor)

        self.promela.write_str(self.triplechoose)
        node.target.accept(self)
        self.promela.write_str(" = ")
        node.value.accept(self)

        return False

    def end_visit_triple(self, node: TripleNode) -> None:
        self.tripletarget = ""
        self.triplechoose = StringManager()
        pass


class FeelToPromelaChooseVisitor(FeelVisitor):
    slots = ["target", "promela", "found_choose"]

    def __init__(self, target: str, promela: StringManager) -> None:
        self.promela = promela
        self.target = target
        self.found_choose: bool = False

    def visit_bool_literal(self, node: BoolLiteralNode) -> bool:
        if self.found_choose:
            self.promela.write_str(node.value)
        return True

    def visit_qualified_name(self, node: QualifiedNameNode) -> bool:
        if self.found_choose:
            self.promela.write_str(node.name)
        return True

    def visit_list(self, node: ListNode) -> bool:
        if self.found_choose:
            self.promela.write_str("{")

            for item in node.values:
                item.accept(self)

                if node.values.index(item) != len(node.values) - 1:
                    self.promela.write_str(", ")

            self.promela.write_str("}")
        return False

    def visit_choose(self, node: ChooseNode) -> bool:
        self.found_choose = True
        type = node.choices.type
        name = self.target

        self.promela.write_str(
            f"mytype:{type} choose_{name}[{len(node.choices.values) - 1}] = "
        )

        node.choices.accept(self)

        self.promela.write_str("", NL_SINGLE)
        self.promela.write_str(f"byte choose_{name}_i = 0", NL_SINGLE)
        self.promela.write_str("atomic{")
        self.promela.write_str(
            f"select(choose_{name}_i : 0..{len(node.choices.values) - 1})"
        )
        self.promela.write_str("}", NL_SINGLE)

        self.found_choose = False
        return False
