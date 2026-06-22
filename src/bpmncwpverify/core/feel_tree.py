class ExpressionNode:
    def accept(self, visitor: "FeelVisitor") -> None:
        pass


class NumberLiteralNode(ExpressionNode):
    __slots__ = ["value"]

    def __init__(self, value: str):
        self.value = value

    def accept(self, visitor: "FeelVisitor") -> None:
        visitor.end_visit_number_literal(self)


class BoolLiteralNode(ExpressionNode):
    __slots__ = ["value"]

    def __init__(self, value: str):
        self.value = value

    def accept(self, visitor: "FeelVisitor") -> None:
        visitor.end_visit_bool_literal(self)


class QualifiedNameNode(ExpressionNode):
    __slots__ = ["name"]

    def __init__(self, name: str):
        self.name = name

    def accept(self, visitor: "FeelVisitor") -> None:
        visitor.end_visit_qualified_name(self)


class ListNode(ExpressionNode):
    __slots__ = ["values"]

    def __init__(self, values: list[ExpressionNode]):
        self.values = values

    def accept(self, visitor: "FeelVisitor") -> None:
        visitor.end_visit_list(self)


class VariableNode(ExpressionNode):
    __slots__ = ["name"]

    def __init__(self, name: str):
        self.name = name

    # def accept(self, visitor: "FeelVisitor"):


class BinaryOperatorNode(ExpressionNode):
    __slots__ = ["left", "right"]

    def __init__(self, left: ExpressionNode, right: ExpressionNode):
        self.left = left
        self.right = right

    def accept(self, visitor: "FeelVisitor") -> None:
        self.left.accept(visitor)
        self.right.accept(visitor)
        visitor.end_visit_binary_operator(self)


class AddNode(BinaryOperatorNode):
    pass
    # def accept(self, visitor: "FeelVisitor") -> None:
    #     self.left.accept(visitor)
    #     self.right.accept(visitor)
    #     visitor.end_visit_add(self)


class SubtractNode(BinaryOperatorNode):
    pass
    # def accept(self, visitor: "FeelVisitor") -> None:
    #     self.left.accept(visitor)
    #     self.right.accept(visitor)
    #     visitor.end_visit_subtract(self)


class MultiplyNode(BinaryOperatorNode):
    pass
    # def accept(self, visitor: "FeelVisitor") -> None:
    #     self.left.accept(visitor)
    #     self.right.accept(visitor)
    #     visitor.end_visit_multiply(self)


class DivideNode(BinaryOperatorNode):
    pass
    # def accept(self, visitor: "FeelVisitor") -> None:
    #     self.left.accept(visitor)
    #     self.right.accept(visitor)
    #     visitor.end_visit_divide(self)


class PowerNode(BinaryOperatorNode):
    pass
    # def accept(self, visitor: "FeelVisitor") -> None:
    #     self.left.accept(visitor)
    #     self.right.accept(visitor)
    #     visitor.end_visit_pow(self)


class ComparisonOperatorNode(ExpressionNode):
    __slots__ = ["left", "right"]

    def __init__(self, left: ExpressionNode, right: ExpressionNode):
        self.left = left
        self.right = right

    def accept(self, visitor: "FeelVisitor") -> None:
        self.left.accept(visitor)
        self.right.accept(visitor)
        visitor.end_visit_comparision(self)


class LTNode(ComparisonOperatorNode):
    pass


class GTNode(ComparisonOperatorNode):
    pass


class LENode(ComparisonOperatorNode):
    pass


class GENode(ComparisonOperatorNode):
    pass


class EqualNode(ComparisonOperatorNode):
    pass


class NotEqualNode(ComparisonOperatorNode):
    pass


class ConditionalOperatorNode(ExpressionNode):
    __slots__ = ["left", "right"]

    def __init__(self, left: ExpressionNode, right: ExpressionNode):
        self.left = left
        self.right = right

    def accept(self, visitor: "FeelVisitor") -> None:
        self.left.accept(visitor)
        self.right.accept(visitor)
        visitor.end_visit_conditional(self)


class AndNode(ConditionalOperatorNode):
    pass


class OrNode(ConditionalOperatorNode):
    pass


class XOrNode(ConditionalOperatorNode):
    pass


class NotNode(ExpressionNode):
    __slots__ = ["expression"]

    def __init__(self, expression: ExpressionNode):
        self.expression = expression

    def accept(self, visitor: "FeelVisitor") -> None:
        visitor.end_visit_not(self)


class IfNode(ExpressionNode):
    __slots__ = ["condition", "thendo", "elsedo"]

    def __init__(
        self, condition: ExpressionNode, thendo: ExpressionNode, elsedo: ExpressionNode
    ):
        self.condition = condition
        self.thendo = thendo
        self.elsedo = elsedo

    def accept(self, visitor: "FeelVisitor") -> None:
        self.condition.accept(visitor)
        self.thendo.accept(visitor)
        self.elsedo.accept(visitor)
        visitor.end_visit_if(self)


class ChooseNode(ExpressionNode):
    __slots__ = ["choices"]

    def __init__(self, choices: ListNode):
        self.choices = choices

    def accept(self, visitor: "FeelVisitor") -> None:  # need to accept on items?
        visitor.end_visit_choose(self)


class TripleNode(ExpressionNode):
    __slots__ = ["target", "inputs", "value"]

    def __init__(self, target: ExpressionNode, inputs: ListNode, value: ExpressionNode):
        self.target = target
        self.inputs = inputs
        self.value = value

    def accept(self, visitor: "FeelVisitor") -> None:
        self.target.accept(visitor)
        self.inputs.accept(visitor)
        self.value.accept(visitor)
        visitor.end_visit_triple(self)


#################
# Generic Visitor
#################


class FeelVisitor:
    def end_visit_number_literal(self, node: NumberLiteralNode) -> None:
        pass

    def end_visit_bool_literal(self, node: BoolLiteralNode) -> None:
        pass

    def end_visit_qualified_name(self, node: QualifiedNameNode) -> None:
        pass

    def end_visit_list(self, node: ListNode) -> None:
        pass

    def end_visit_binary_operator(self, node: BinaryOperatorNode) -> None:
        pass

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
        pass

    def end_visit_conditional(self, node: ConditionalOperatorNode) -> None:
        pass

    def end_visit_not(self, node: NotNode) -> None:
        pass

    def end_visit_if(self, node: IfNode) -> None:
        pass

    def end_visit_choose(self, node: ChooseNode) -> None:
        pass

    def end_visit_triple(self, node: TripleNode) -> None:
        pass
