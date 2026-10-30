from returns.maybe import Nothing, Some
from returns.pipeline import is_successful

from bpmncwpverify.core.error import (
    ErrorException,
    ExpressionComputationCompatabilityError,
    ExpressionIfBranchCompatabilityError,
    ExpressionIfConditionError,
    ExpressionLogicalCompatibilityError,
    ExpressionOutOfScope,
    ExpressionRelationalNotError,
    ExpressionRelationCompatabilityError,
    ExpressionTripleInputError,
    ExpressionUnrecognizedID,
    IntervalValidationError,
    TypingAssignCompatabilityError,
    TypingListCompatibiltiyError,
    TypingListOfExpressionsError,
    TypingNotCaughtError,
    TypingNoTypeError,
    TypingTripleVariableError,
)
from bpmncwpverify.core.feel_tree import (
    AddNode,
    BinaryOperatorNode,
    BoolLiteralNode,
    ChooseNode,
    ComparisonOperatorNode,
    ConditionalOperatorNode,
    DivideNode,
    ExpressionNode,
    FeelVisitor,
    IfNode,
    IntervalNode,
    ListNode,
    MultiplyNode,
    NotNode,
    NumberLiteralNode,
    PowerNode,
    QualifiedNameNode,
    SubtractNode,
    TripleListNode,
    TripleNode,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.core.typechecking import (
    BOOL,
    get_and_or_type_result,
    get_computation_type_result,
    get_relational_type_result,
    get_type_assign,
    get_type_literal,
    get_widened_type_result,
    is_integer_type,
)


class TypeCheckerVisitor(FeelVisitor):
    __slots__ = ["state", "stack"]

    def __init__(self, state: State):
        self.state = state
        self.stack: list[str] = []

    def is_leaf(self, node: ExpressionNode) -> bool:
        if isinstance(node, NumberLiteralNode):
            return True
        elif isinstance(node, BoolLiteralNode):
            return True
        elif isinstance(node, QualifiedNameNode):
            return True
        else:
            return False

    def end_visit_number_literal(self, node: NumberLiteralNode) -> None:
        type = get_type_literal(node.value)

        if is_successful(type):
            self.stack.append(type.unwrap())
        else:
            raise ErrorException(TypingNoTypeError(node.value))

    def end_visit_bool_literal(self, node: BoolLiteralNode) -> None:
        type = get_type_literal(node.value)

        if is_successful(type):
            self.stack.append(type.unwrap())

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        if self.state.is_variable(node.name):
            self.stack.append(self.state.get_type(node.name).unwrap())
        elif self.state.is_enum(node.name):
            self.stack.append(self.state.get_type(node.name).unwrap())
        elif self.state.is_constant(node.name):
            self.stack.append(self.state.get_type(node.name).unwrap())
        else:
            raise ErrorException(ExpressionUnrecognizedID(node.name))

    def visit_list(self, node: ListNode) -> bool:
        for item in node.values:
            if not self.is_leaf(item):
                raise ErrorException(TypingListOfExpressionsError())

        return True

    def end_visit_list(self, node: ListNode) -> None:
        items = len(node.values)
        if items == 0:
            self.stack.append("None")
        else:
            first = self.stack[len(self.stack) - items]
            for _ in range(items):
                next = self.stack.pop()
                new_type = get_widened_type_result(first, next)
                if not is_successful(new_type):
                    raise ErrorException(TypingListCompatibiltiyError(first, next))
                first = new_type.unwrap()
            self.stack.append(first)
            node.type = Some(first)

    def visit_interval(self, node: IntervalNode) -> bool:
        raise ErrorException(
            IntervalValidationError("Intervals are only supported through choose")
        )

    def end_visit_binary_operator(self, node: BinaryOperatorNode) -> None:
        right = self.stack.pop()
        left = self.stack.pop()

        type = get_computation_type_result(left, right)

        if is_successful(type):
            self.stack.append(type.unwrap())
        else:
            raise ErrorException(ExpressionComputationCompatabilityError(left, right))

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
        else:
            raise ErrorException(ExpressionRelationCompatabilityError(left, right))

    def end_visit_conditional(self, node: ConditionalOperatorNode) -> None:
        right = self.stack.pop()
        left = self.stack.pop()

        type = get_and_or_type_result(left, right)

        if is_successful(type):
            self.stack.append(type.unwrap())
        else:
            raise ErrorException(ExpressionLogicalCompatibilityError(left, right))

    def end_visit_not(self, node: NotNode) -> None:
        type = self.stack.pop()

        if type == BOOL:
            self.stack.append(type)
        else:
            raise ErrorException(ExpressionRelationalNotError(type))

    def end_visit_if(self, node: IfNode) -> None:
        elsedo_type = self.stack.pop()
        thendo_type = self.stack.pop()
        cond_type = self.stack.pop()

        if cond_type == BOOL:
            result_type = get_widened_type_result(thendo_type, elsedo_type)

            if is_successful(result_type):
                self.stack.append(result_type.unwrap())
            else:
                raise ErrorException(
                    ExpressionIfBranchCompatabilityError(thendo_type, elsedo_type)
                )
        else:
            raise ErrorException(ExpressionIfConditionError(cond_type))

    def visit_choose(self, node: ChooseNode) -> bool:
        if isinstance(node.choices, IntervalNode):
            interval_node = node.choices
            interval_node.type = Nothing

            if not isinstance(interval_node.lower, NumberLiteralNode) or not isinstance(
                interval_node.upper, NumberLiteralNode
            ):
                raise ErrorException(
                    IntervalValidationError("Interval bounds must be integer literals")
                )

            interval_node.lower.accept(self)
            interval_node.upper.accept(self)

            upper_type = self.stack.pop()
            lower_type = self.stack.pop()

            if not is_integer_type(lower_type) or not is_integer_type(upper_type):
                raise ErrorException(
                    IntervalValidationError("Interval bounds must have integer types")
                )

            interval_type = get_widened_type_result(lower_type, upper_type)
            if not is_successful(interval_type):
                raise ErrorException(
                    IntervalValidationError(
                        "Interval bounds have incompatible integer types"
                    )
                )

            lower = int(interval_node.lower.value)
            upper = int(interval_node.upper.value)

            if lower < 0 or upper < 0:
                raise ErrorException(
                    IntervalValidationError("Interval bounds must be nonnegative")
                )

            if lower > upper:
                raise ErrorException(
                    IntervalValidationError(
                        "Interval lower bound must not exceed upper bound"
                    )
                )

            first = lower + (not interval_node.lower_inclusive)
            last = upper - (not interval_node.upper_inclusive)
            if first > last:
                raise ErrorException(
                    IntervalValidationError(
                        "Interval must contain at least one integer"
                    )
                )

            interval_node.type = Some(interval_type.unwrap())
            self.stack.append(interval_type.unwrap())

            return False

        return True

    def end_visit_choose(self, node: ChooseNode) -> None:
        element_type = self.stack.pop()

        self.stack.append(element_type)

    def visit_triple(self, node: TripleNode) -> bool:
        target_input_visitor = TypeCheckerTripleInputTargetVisitor(
            self.stack, self.state
        )
        value_visitor = TypeCheckerTripleValueVisitor(self.stack, self.state)
        value_visitor.scope = []

        for input in node.inputs.values:
            if isinstance(input, QualifiedNameNode):
                value_visitor.scope.append(input.name)
            else:
                raise ErrorException(ExpressionTripleInputError())

        node.inputs.accept(target_input_visitor)
        node.value.accept(value_visitor)

        if not isinstance(node.target, QualifiedNameNode):
            raise ErrorException(
                TypingNotCaughtError(
                    "TYPE ERROR: frist argument in triple needs to be a qualifiedNameNode and typechecker did not catch it."
                )
            )
        node.target.accept(target_input_visitor)

        return False

    def end_visit_triple(self, node: TripleNode) -> None:
        target_type = self.stack.pop()
        value_type = self.stack.pop()
        self.stack.pop()  # input types

        result_type = get_type_assign(target_type, value_type)

        if is_successful(result_type):
            self.stack.append(result_type.unwrap())
        else:
            raise ErrorException(
                TypingAssignCompatabilityError(target_type, value_type)
            )

    def end_visit_triple_list(self, node: TripleListNode) -> None:
        for _ in range(len(node.triples)):
            self.stack.pop()
        self.stack.append("triples")


class TypeCheckerTripleInputTargetVisitor(TypeCheckerVisitor):
    __slots__ = ["stack", "state"]

    def __init__(self, stack: list[str], state: State) -> None:
        self.stack = stack
        self.state = state

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        if self.state.is_variable(node.name):
            self.stack.append(self.state.get_type(node.name).unwrap())
        elif self.state.is_enum(node.name):
            raise ErrorException(TypingTripleVariableError(node.name))
        else:
            raise ErrorException(ExpressionUnrecognizedID(node.name))

    def end_visit_list(self, node: ListNode) -> None:
        items = len(node.values)
        if items == 0:
            self.stack.append("None")
        else:
            for _ in range(items):
                self.stack.pop()
            self.stack.append("None")
            node.type = Nothing


class TypeCheckerTripleValueVisitor(TypeCheckerVisitor):
    __slots__ = ["stack", "state", "scope"]

    def __init__(self, stack: list[str], state: State) -> None:
        self.stack = stack
        self.state = state
        self.scope: list[str] = []

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        if self.state.is_variable(node.name):
            if node.name in self.scope:
                self.stack.append(self.state.get_type(node.name).unwrap())
            else:
                raise ErrorException(ExpressionOutOfScope(node.name))
        elif self.state.is_enum(node.name):
            self.stack.append(self.state.get_type(node.name).unwrap())
        elif self.state.is_constant(node.name):
            self.stack.append(self.state.get_type(node.name).unwrap())
        else:
            raise ErrorException(ExpressionUnrecognizedID(node.name))

    def end_visit_list(self, node: ListNode) -> None:
        items = len(node.values)
        if items == 0:
            self.stack.append("None")
        else:
            first = self.stack[len(self.stack) - items]
            for _ in range(items):
                next = self.stack.pop()
                new_type = get_widened_type_result(first, next)
                if not is_successful(new_type):
                    raise ErrorException(TypingListCompatibiltiyError(first, next))
                first = new_type.unwrap()
            self.stack.append(first)
            node.type = Some(first)
