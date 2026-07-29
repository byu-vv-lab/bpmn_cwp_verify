from returns.maybe import Nothing

from bpmncwpverify.core.error import ErrorException, TypingNotCaughtError
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
    NotEqualNode,
    NotNode,
    NumberLiteralNode,
    OrNode,
    QualifiedNameNode,
    SubtractNode,
    TripleListNode,
    TripleNode,
    XOrNode,
)
from bpmncwpverify.util.stringmanager import NL_SINGLE, StringManager


class FeelToPromelaVisitor(FeelVisitor):
    __slots__ = ["promela", "choose", "choose_id", "index"]

    def __init__(self, choose_id: str) -> None:
        self.promela = StringManager()
        self.choose = StringManager()
        self.choose_id = choose_id
        self.index: int = 0

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

    def visit_binary_operator(self, node: BinaryOperatorNode) -> bool:
        self.promela.write_str("(")
        node.left.accept(self)

        match node:
            case AddNode():
                self.promela.write_str(" + ")
            case SubtractNode():
                self.promela.write_str(" - ")
            case MultiplyNode():
                self.promela.write_str(" * ")
            case DivideNode():
                self.promela.write_str(" / ")
            case _:
                raise ErrorException(
                    TypingNotCaughtError(
                        "TYPE ERROR: Type checker did not catch none valid symbol"
                    )
                )

        node.right.accept(self)
        self.promela.write_str(")")

        return False

    def visit_comparision(self, node: ComparisonOperatorNode) -> bool:
        self.promela.write_str("(")
        node.left.accept(self)

        match node:
            case LTNode():
                self.promela.write_str(" < ")
            case GTNode():
                self.promela.write_str(" > ")
            case LENode():
                self.promela.write_str("<=")
            case GENode():
                self.promela.write_str(" >= ")
            case EqualNode():
                self.promela.write_str(" == ")
            case NotEqualNode():
                self.promela.write_str(" != ")
            case _:
                raise ErrorException(
                    TypingNotCaughtError(
                        "TYPE ERROR: Type checker did not catch none valid symbol"
                    )
                )

        node.right.accept(self)
        self.promela.write_str(")")
        return False

    def visit_conditional(self, node: ConditionalOperatorNode) -> bool:
        self.promela.write_str("(")
        node.left.accept(self)

        match node:
            case AndNode():
                self.promela.write_str(" && ")
            case OrNode():
                self.promela.write_str(" || ")
            case XOrNode():
                self.promela.write_str(" && ")
                self.promela.write_str("!")
                node.right.accept(self)
                self.promela.write_str(" || ")
                self.promela.write_str("!")
                node.left.accept(self)
                self.promela.write_str(" && ")
            case _:
                raise ErrorException(
                    TypingNotCaughtError(
                        "TYPE ERROR: Type checker did not catch none valid symbol"
                    )
                )

        node.right.accept(self)
        self.promela.write_str(")")
        return False

    def visit_not(self, node: NotNode) -> bool:
        self.promela.write_str("!")
        return True

    def visit_if(self, node: IfNode) -> bool:
        self.promela.write_str("(")

        node.condition.accept(self)

        self.promela.write_str(" -> ")

        node.thendo.accept(self)

        self.promela.write_str(" : ")

        node.elsedo.accept(self)

        self.promela.write_str(")")

        return False

    def visit_choose(self, node: ChooseNode) -> bool:
        choose_visitor = FeelToPromelaChooseVisitor(self.choose, self.choose_id)
        node.accept(choose_visitor)

        self.promela.write_str(
            f"choose_{self.choose_id}[choose_{self.choose_id}_i]", NL_SINGLE
        )
        self.promela.write_str("atomic{")
        self.promela.write_str(
            f"select(choose_{self.choose_id}_i : 0..{len(node.choices.values) - 1})"
        )
        self.promela.write_str("}", NL_SINGLE)
        self.index += 1
        return False

    def visit_triple(self, node: TripleNode) -> bool:
        node.target.accept(self)
        self.promela.write_str(" = ")
        node.value.accept(self)

        return False

    def end_visit_triple(self, node: TripleNode) -> None:
        pass

    def visit_triple_list(self, node: TripleListNode) -> bool:
        for triple in node.triples:
            triple.accept(self)
            self.promela.write_str("", NL_SINGLE)

        return False

    def end_visit_triple_list(self, node: TripleListNode) -> None:
        pass


class FeelToPromelaChooseVisitor(FeelVisitor):
    slots = ["promela", "found_choose", "choose_id"]

    def __init__(self, promela: StringManager, choose_id: str) -> None:
        self.promela = promela
        self.found_choose: bool = False
        self.choose_id = choose_id

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
        if node.choices.type == Nothing:
            raise ErrorException(
                TypingNotCaughtError(
                    "TYPE ERROR: list does not have a type and was not caught by the type checker"
                )
            )
        type = node.choices.type.unwrap()

        if type == "byte":
            self.promela.write_str(
                f"{type} choose_{self.choose_id}[{len(node.choices.values)}] = "
            )
        else:
            self.promela.write_str(
                f"mtype:{type} choose_{self.choose_id}[{len(node.choices.values)}] = "
            )

        node.choices.accept(self)

        self.promela.write_str("", NL_SINGLE)
        self.promela.write_str(f"byte choose_{self.choose_id}_i = 0", NL_SINGLE)

        self.found_choose = False
        return False
