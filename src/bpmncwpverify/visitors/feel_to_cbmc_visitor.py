from bpmncwpverify.core.error import (
    CbmcUnsupportedElementError,
    ErrorException,
    TypingNotCaughtError,
)
from bpmncwpverify.core.feel import Feel
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
    ExpressionNode,
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


class FeelToCbmcVisitor(FeelVisitor):
    """Translates a FEEL AST into CBMC C.

    `expr` accumulates the expression currently being built (guard/comparison
    text, or scratch state while building a triple's target/value). `stmts`
    collects completed C statement lines (assignments, and any
    `nondet_int()`/`__CPROVER_assume()` pairs a `choose(...)` needs).
    """

    __slots__ = ["expr", "stmts", "choose_id", "_choose_idx"]

    def __init__(self, choose_id: str) -> None:
        self.expr: str = ""
        self.stmts: list[str] = []
        self.choose_id = choose_id
        self._choose_idx: int = 0

    def _render(self, node: ExpressionNode) -> str:
        """Render `node` in isolation without disturbing the current `expr`."""
        saved = self.expr
        self.expr = ""
        node.accept(self)
        rendered = self.expr
        self.expr = saved
        return rendered

    def visit_number_literal(self, node: NumberLiteralNode) -> bool:
        self.expr += node.value
        return True

    def visit_bool_literal(self, node: BoolLiteralNode) -> bool:
        self.expr += node.value
        return True

    def visit_qualified_name(self, node: QualifiedNameNode) -> bool:
        self.expr += node.name
        return True

    def visit_list(self, node: ListNode) -> bool:
        self.expr += "{"

        for i, item in enumerate(node.values):
            if i:
                self.expr += ", "
            item.accept(self)

        self.expr += "}"
        return False

    def visit_binary_operator(self, node: BinaryOperatorNode) -> bool:
        self.expr += "("
        node.left.accept(self)

        match node:
            case AddNode():
                self.expr += " + "
            case SubtractNode():
                self.expr += " - "
            case MultiplyNode():
                self.expr += " * "
            case DivideNode():
                self.expr += " / "
            case _:
                raise ErrorException(
                    TypingNotCaughtError(
                        "TYPE ERROR: Type checker did not catch none valid symbol"
                    )
                )

        node.right.accept(self)
        self.expr += ")"
        return False

    def visit_comparision(self, node: ComparisonOperatorNode) -> bool:
        self.expr += "("
        node.left.accept(self)

        match node:
            case LTNode():
                self.expr += " < "
            case GTNode():
                self.expr += " > "
            case LENode():
                self.expr += " <= "
            case GENode():
                self.expr += " >= "
            case EqualNode():
                self.expr += " == "
            case NotEqualNode():
                self.expr += " != "
            case _:
                raise ErrorException(
                    TypingNotCaughtError(
                        "TYPE ERROR: Type checker did not catch none valid symbol"
                    )
                )

        node.right.accept(self)
        self.expr += ")"
        return False

    def visit_conditional(self, node: ConditionalOperatorNode) -> bool:
        self.expr += "("
        node.left.accept(self)

        match node:
            case AndNode():
                self.expr += " && "
            case OrNode():
                self.expr += " || "
            case XOrNode():
                # Both operands are guaranteed bool by the type checker, so
                # C's != is exact boolean XOR — no need for Promela's
                # (L && !R) || (!L && R) expansion.
                self.expr += " != "
            case _:
                raise ErrorException(
                    TypingNotCaughtError(
                        "TYPE ERROR: Type checker did not catch none valid symbol"
                    )
                )

        node.right.accept(self)
        self.expr += ")"
        return False

    def visit_not(self, node: NotNode) -> bool:
        self.expr += "!"
        return True

    def visit_if(self, node: IfNode) -> bool:
        if isinstance(node.thendo, TripleNode | TripleListNode) or isinstance(
            node.elsedo, TripleNode | TripleListNode
        ):
            raise ErrorException(
                CbmcUnsupportedElementError(
                    self.choose_id,
                    "if-expression used to conditionally assign different targets",
                )
            )

        self.expr += "("
        node.condition.accept(self)
        self.expr += " ? "
        node.thendo.accept(self)
        self.expr += " : "
        node.elsedo.accept(self)
        self.expr += ")"
        return False

    def visit_choose(self, node: ChooseNode) -> bool:
        t_var = f"t_choose_{self.choose_id}_{self._choose_idx}"
        self._choose_idx += 1

        value_texts = [self._render(value) for value in node.choices.values]

        self.stmts.append(f"int {t_var} = nondet_int();")
        assume = " || ".join(f"{t_var} == {value}" for value in value_texts)
        self.stmts.append(f"__CPROVER_assume({assume});")

        self.expr += t_var
        return False

    def visit_triple(self, node: TripleNode) -> bool:
        target = self._render(node.target)
        value = self._render(node.value)
        self.stmts.append(f"{target} = {value};")
        return False

    def visit_triple_list(self, node: TripleListNode) -> bool:
        for triple in node.triples:
            triple.accept(self)
        return False


def translate_feel_expr(expression: "str | Feel", owner_id: str) -> str:
    """Render a guard/edge-condition value (Feel AST or legacy plain string) as C."""
    if not isinstance(expression, Feel):
        return str(expression)

    visitor = FeelToCbmcVisitor(owner_id)
    expression.ast.accept(visitor)

    if visitor.stmts:
        raise ErrorException(
            CbmcUnsupportedElementError(
                owner_id,
                "Feel guard/edge expression requires preamble statements "
                "(e.g. a nested choose()), unsupported in this position",
            )
        )

    return visitor.expr


def translate_feel_behavior(behavior: Feel, owner_id: str) -> tuple[list[str], bool]:
    """Render a Task's FEEL behavior AST as CBMC C statement lines.

    Returns (lines, always_assigns). Every supported shape here is a
    straight-line sequence of assignments (if-as-statement-block is rejected
    in visit_if), so always_assigns is unconditionally True.
    """
    if not isinstance(behavior.ast, TripleNode | TripleListNode):
        raise ErrorException(
            CbmcUnsupportedElementError(owner_id, type(behavior.ast).__name__)
        )

    visitor = FeelToCbmcVisitor(owner_id)
    behavior.ast.accept(visitor)
    return visitor.stmts, True
