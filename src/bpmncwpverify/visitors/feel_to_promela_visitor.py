from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BinaryOperatorNode,
    BoolLiteralNode,
    ChooseNode,
    ComparisonOperatorNode,
    ConditionalOperatorNode,
    DivideNode,
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
from bpmncwpverify.util.stringmanager import NL_SINGLE, IndentAction, StringManager


class FeelToPromelaVisitor(FeelVisitor):
    __slots__ = ["promela"]

    def __init__(self) -> None:
        self.promela = StringManager()

    def end_visit_number_literal(self, node: NumberLiteralNode) -> None:
        pass

    def end_visit_bool_literal(self, node: BoolLiteralNode) -> None:
        self.promela.write_str(node.value)

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        self.promela.write_str(node.name)

    def visit_list(self, node: ListNode) -> bool:
        return True

    def end_visit_list(self, node: ListNode) -> None:
        pass

    def visit_binary_operator(self, node: BinaryOperatorNode) -> bool:
        node.left.accept(self)

        if isinstance(node, AddNode):
            self.promela.write_str(" + ")
        elif isinstance(node, SubtractNode):
            self.promela.write_str(" - ")
        elif isinstance(node, MultiplyNode):
            self.promela.write_str(" * ")
        elif isinstance(node, DivideNode):
            self.promela.write_str(" / ")  # need to work this out
        else:
            self.promela.write_str(" ** ")

        return False

    def end_visit_binary_operator(self, node: BinaryOperatorNode) -> None:
        pass

    def visit_comparision(self, node: ComparisonOperatorNode) -> bool:
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
            self.promela.write_str(" = ")
        else:
            self.promela.write_str(" != ")

        node.right.accept(self)
        return False

    def end_visit_comparision(self, node: ComparisonOperatorNode) -> None:
        pass

    def visit_conditional(self, node: ConditionalOperatorNode) -> bool:
        node.left.accept(self)

        if isinstance(node, AndNode):
            self.promela.write_str(" && ")
        elif isinstance(node, OrNode):
            self.promela.write_str(" || ")
        else:
            self.promela.write_str("")  # need to figure this one out

        node.right.accept(self)
        return False

    def end_visit_conditional(self, node: ConditionalOperatorNode) -> None:
        pass

    def visit_not(self, node: NotNode) -> bool:
        return True

    def end_visit_not(self, node: NotNode) -> None:
        pass

    def visit_if(self, node: IfNode) -> bool:
        self.promela.write_str("if", NL_SINGLE)
        self.promela.write_str(":: ")

        node.condition.accept(self)

        self.promela.write_str(" -> ")

        node.thendo.accept(self)

        self.promela.write_str("", NL_SINGLE)
        self.promela.write_str(":: else -> ")

        node.elsedo.accept(self)

        self.promela.write_str("", NL_SINGLE)
        self.promela.write_str("fi")

        return False

    def end_visit_if(self, node: IfNode) -> None:
        pass

    def visit_choose(self, node: ChooseNode) -> bool:
        self.promela.write_str("if", NL_SINGLE, IndentAction.INC)

        for item in node.choices.values:
            self.promela.write_str(":: True -> ")
            item.accept(self)
            self.promela.write_str("= ")

        return True

    def end_visit_choose(self, node: ChooseNode) -> None:
        pass

    def visit_triple(self, node: TripleNode) -> bool:
        return True

    def end_visit_triple(self, node: TripleNode) -> None:
        pass


class FeelToPromelaTripleVisitor(FeelVisitor):
    slots = ["target", "inputs", "promela"]

    def __init__(self, promela: StringManager) -> None:
        self.promela = promela
        self.target: str = ""
        self.inputs: list[str] = []

    def visit_triple(self, node: TripleNode) -> bool:
        return True

    def end_visit_triple(self, node: TripleNode) -> None:
        pass
