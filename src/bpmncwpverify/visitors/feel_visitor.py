from typing import cast

from bpmncwpverify.antlr.FeelExprParser import FeelExprParser
from bpmncwpverify.antlr.FeelExprVisitor import FeelExprVisitor
from bpmncwpverify.core.feel_tree import (
    AddNode,
    DivideNode,
    ExpressionNode,
    LiteralNode,
    MultiplyNode,
    SubNode,
    VariableNode,
)


class FeelExprBuilder(FeelExprVisitor):
    """
    Tree visitor that builds an AST from the FEEL parse tree.
    Returns appropriate ExpressionNode subclasses for each rule.
    """

    # def visitChildren(self, node):
    #     print(f"visitChildren called for: {node.__class__.__name__}")
    #     return super().visitChildren(node)

    # def visit(self, tree):
    #     method_name = "visit" + tree.__class__.__name__
    #     print(f"Looking for method: {method_name}")
    #     method = getattr(self, method_name, None)
    #     print(f"Found method: {method}")
    #     return super().visit(tree)

    def visitCompilation_unitContext(self, ctx: FeelExprParser.Compilation_unitContext) -> ExpressionNode: # type: ignore[override]
        expr = cast(FeelExprParser.ExpressionContext, ctx.expression())
        return cast(ExpressionNode, self.visit(expr))

    def visitExpressionTextualContext(self, ctx: FeelExprParser.ExpressionTextualContext) -> ExpressionNode:   # type: ignore[override]
        return cast(ExpressionNode, self.visit(cast(FeelExprParser.TextualExpressionContext, ctx.textualExpression())))

    def visitTextualExpressionContext(self, ctx: FeelExprParser.TextualExpressionContext) -> ExpressionNode:   # type: ignore[override]
        return cast(ExpressionNode, self.visit(cast(FeelExprParser.ConditionalOrExpressionContext, ctx.conditionalOrExpression())))

    def visitAddExpressionContext(self, ctx: FeelExprParser.AddExpressionContext) -> ExpressionNode:   # type: ignore[override]
        left = cast(ExpressionNode, self.visit(cast(FeelExprParser.AdditiveExpressionContext, ctx.additiveExpression())))
        right = cast(ExpressionNode, self.visit(cast(FeelExprParser.MultiplicativeExpressionContext, ctx.multiplicativeExpression())))

        if ctx.ADD():
            return AddNode(left, right)
        else:
            return SubNode(left, right)

    def visitAddExpressionMultContext(self, ctx: FeelExprParser.AddExpressionMultContext) -> ExpressionNode:   # type: ignore[override]
        return cast(ExpressionNode, self.visit(cast(FeelExprParser.MultiplicativeExpressionContext, ctx.multiplicativeExpression())))

    def visitNumberLiteralContext(self, ctx: FeelExprParser.NumberLiteralContext) -> ExpressionNode:   # type: ignore[override]
        return LiteralNode(float(ctx.getText()))

    def visitPrimaryNameContext(self, ctx: FeelExprParser.PrimaryNameContext) -> ExpressionNode:   # type: ignore[override]
        return VariableNode(cast(str, ctx.qualifiedName()))

    def visitMultExpressionContext(self, ctx: FeelExprParser.MultExpressionContext) -> ExpressionNode: # type: ignore[override]
        left = cast(ExpressionNode, self.visit(cast(FeelExprParser.MultiplicativeExpressionContext, ctx.multiplicativeExpression())))
        right = cast(ExpressionNode, self.visit(cast(FeelExprParser.PowerExpressionContext, ctx.powerExpression())))

        if ctx.MUL():
            return MultiplyNode(left, right)
        else:
            return DivideNode(left, right)

    def visitCondOrAndContext(self, ctx:FeelExprParser.CondOrAndContext) -> ExpressionNode: # type: ignore[override]
        return cast(ExpressionNode, self.visit(cast(FeelExprParser.ComparisonExpressionContext, ctx.conditionalAndExpression())))
    
    def visitCondAndCompContext(self, ctx:FeelExprParser.CondAndCompContext) -> ExpressionNode: # type: ignore[override]
        pass
