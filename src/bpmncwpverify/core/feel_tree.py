from typing import cast


class ExpressionNode:
    def evaluate(self, variables: dict[str, float]) -> float:
        raise NotImplementedError


class NumberLiteralNode(ExpressionNode):
    __slots__ = ["value"]

    def __init__(self, value: str):
        self.value = value


class BoolLiteralNode(ExpressionNode):
    __slots__ = ["value"]

    def __init__(self, value: bool):
        self.value = value


class QualifiedNameNode(ExpressionNode):
    __slots__ = ["name"]

    def __init__(self, name: str):
        self.name = name


class ListNode(ExpressionNode):
    __slots__ = ["values"]

    def __init__(self, values: list[ExpressionNode]):
        self.values = values


class VariableNode(ExpressionNode):
    __slots__ = ["name"]

    def __init__(self, name: str):
        self.name = name

    def evaluate(self, variables: dict[str, float]) -> float:
        return variables[self.name]


class BinaryOperatorNode(ExpressionNode):
    __slots__ = ["left", "right"]

    def __init__(self, left: ExpressionNode, right: ExpressionNode):
        self.left = left
        self.right = right


class AddNode(BinaryOperatorNode):
    def evaluate(self, variables: dict[str, float]) -> float:
        return self.left.evaluate(variables) + self.right.evaluate(variables)


class SubNode(BinaryOperatorNode):
    def evaluate(self, variables: dict[str, float]) -> float:
        return self.left.evaluate(variables) - self.right.evaluate(variables)


class MultiplyNode(BinaryOperatorNode):
    def evaluate(self, variables: dict[str, float]) -> float:
        return self.left.evaluate(variables) * self.right.evaluate(variables)


class DivideNode(BinaryOperatorNode):
    def evaluate(self, variables: dict[str, float]) -> float:
        return self.left.evaluate(variables) / self.right.evaluate(variables)


class PowerNode(BinaryOperatorNode):
    def evaluate(self, variables: dict[str, float]) -> float:
        return cast(
            float, self.left.evaluate(variables) ** self.right.evaluate(variables)
        )


class ComparisonOperatorNode(ExpressionNode):
    __slots__ = ["left", "right"]

    def __init__(self, left: ExpressionNode, right: ExpressionNode):
        self.left = left
        self.right = right


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


class IfNode(ExpressionNode):
    __slots__ = ["condition", "thendo", "elsedo"]

    def __init__(
        self, condition: ExpressionNode, thendo: ExpressionNode, elsedo: ExpressionNode
    ):
        self.condition = condition
        self.thendo = thendo
        self.elsedo = elsedo


class ChooseNode(ExpressionNode):
    __slots__ = ["choices"]

    def __init__(self, choices: ListNode):
        self.choices = choices


class TripleNode(ExpressionNode):
    __slots__ = ["target", "inputs", "value"]

    def __init__(self, target: ExpressionNode, inputs: ListNode, value: ExpressionNode):
        self.target = target
        self.inputs = inputs
        self.value = value
