# from antlr4 import ParseTreeVisitor

# from bpmncwpverify.antlr.FeelExprParser import FeelExprParser
# from bpmncwpverify.core.feel_tree import *


# class FeelExprVisitor(ParseTreeVisitor):
#     """
#     Tree visitor that builds an AST from the FEEL parse tree.
#     Returns appropriate ExpressionNode subclasses for each rule.
#     """

# def visitComplilation_unit(self, ctx: FeelExprParser.Compilation_unitContext):
#     return self.visit(ctx.expression())

# def visitExpresssionTextual(self, ctx: FeelExprParser.ExpressionTextualContext):
#     return self.visit(ctx.textualExpression())

# def visitAdditiveExpression(self, ctx: FeelExprParser.AdditiveExpressionContext):
#     left = self.visit(ctx.additiveExpression())
#     right = self.visit(ctx.multiplicativeExpression())

#     if ctx.op == FeelExprParser.ADD:
#         return AddNode(left, right)
#     else:
#         return SubNode(left, right)

# def visitLiteral(self, ctx: FeelExprParser.LiteralContext):
#     return LiteralNode(ctx.getText())

# def visitNameRef(self, ctx: FeelExprParser.NameRefContext):
#     return VariableNode(ctx.Identifier())

# def visitMultiplicativeEpression(
#     self, ctx: FeelExprParser.MultiplicativeExpressionContext
# ):
#     left = self.visit(ctx.left)
#     right = self.visit(ctx.right)

#     if "*" in ctx.getText():
#         return MultiplyNode(left, right)
#     else:
#         return DivideNode(left, right)
