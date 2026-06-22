from typing import cast

from returns.pipeline import is_successful

from bpmncwpverify.core.feel_tree import (
    AddNode,
    BinaryOperatorNode,
    BoolLiteralNode,
    ChooseNode,
    ComparisonOperatorNode,
    ConditionalOperatorNode,
    DivideNode,
    FeelVisitor,
    IfNode,
    ListNode,
    MultiplyNode,
    NotNode,
    NumberLiteralNode,
    PowerNode,
    QualifiedNameNode,
    SubtractNode,
    TripleNode,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.core.typechecking import (
    BOOL,
    get_and_or_type_result,
    get_computation_type_result,
    get_relational_type_result,
    get_type_literal,
)


class TypeCheckerVisitor(FeelVisitor):
    __slots__ = ["state", "stack"]

    def __init__(self, state: State):
        self.state = state
        self.stack: list[str] = []

    def end_visit_number_literal(self, node: NumberLiteralNode) -> None:
        type = get_type_literal(node.value)

        if is_successful(type):
            self.stack.append(type.unwrap())

    def end_visit_bool_literal(self, node: BoolLiteralNode) -> None:
        type = get_type_literal(node.value)

        if is_successful(type):
            self.stack.append(type.unwrap())

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        valid = self.state.is_variable(node.name)

        if valid:
            self.stack.append(self.state.get_type(node.name).unwrap())
        else:
            # raise error
            pass

    def end_visit_list(self, node: ListNode) -> None:
        pass  # accept on each thing and then pop each and everyone checking

    def end_visit_binary_operator(self, node: BinaryOperatorNode) -> None:
        right = self.stack.pop()
        left = self.stack.pop()

        type = get_computation_type_result(left, right)

        if is_successful(type):
            self.stack.append(type.unwrap())
        else:
            pass  # error

    def end_visit_add(self, node: AddNode) -> None:
        pass

    def end_visit_subtract(self, node: SubtractNode) -> None:
        pass

    def end_visit_multiply(self, node: MultiplyNode) -> None:
        pass

    def end_visit_divide(self, node: DivideNode) -> None:
        pass

    def end_visit_pow(self, node: PowerNode) -> None:
        pass

    def end_visit_comparision(self, node: ComparisonOperatorNode) -> None:
        right = self.stack.pop()
        left = self.stack.pop()

        type = get_relational_type_result(left, right)

        if is_successful(type):
            self.stack.append(type.unwrap())

    def end_visit_conditional(self, node: ConditionalOperatorNode) -> None:
        right = self.stack.pop()
        left = self.stack.pop()

        type = get_and_or_type_result(left, right)

        if is_successful(type):
            self.stack.append(type.unwrap())

    def end_visit_not(self, node: NotNode) -> None:
        type = get_type_literal(self.stack.pop())

        if is_successful(type) and type.unwrap() == BOOL:  # check this
            self.stack.append(type.unwrap())
        else:
            pass  # error

    def end_visit_if(self, node: IfNode) -> None:
        elsedo = self.stack.pop()
        thendo = self.stack.pop()
        cond = self.stack.pop()

        cond_type = get_type_literal(cond)
        if is_successful(cond_type) and cond_type.unwrap() == BOOL:
            if thendo == elsedo:
                self.stack.append(thendo)
            else:
                pass  # return type mismatch
        else:
            pass  # condition issue

    def end_visit_choose(self, node: ChooseNode) -> None:
        list_type = self.stack.pop()

        self.stack.append(list_type)

    def end_visit_triple(self, node: TripleNode) -> None:  # not done
        value_type = self.stack.pop()
        # inputs_type = self.stack.pop()
        target_type = self.stack.pop()

        if self.state.is_variable(cast(QualifiedNameNode, node.target).name):
            if target_type == value_type:
                self.stack.append(target_type)
            else:
                pass  # incompatably types
        else:
            pass  # not possible assignemtn
