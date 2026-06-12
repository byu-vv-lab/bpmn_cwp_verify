class ExpressionNode:
    def evaluate(self, variables: dict[str, float]) -> float:
        raise NotImplementedError


class LiteralNode(ExpressionNode):
    __slots__ = ["value"]

    def __init__(self, value: float):
        self.value = value

    def evaluate(self, variables: dict[str, float]) -> float:
        return self.value


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
