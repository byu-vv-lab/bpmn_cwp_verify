# Generated from antlr/CwpParser.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .CwpParser import CwpParser
else:
    from CwpParser import CwpParser

# This class defines a complete generic visitor for a parse tree produced by CwpParser.

class CwpParserVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by CwpParser#diagram.
    def visitDiagram(self, ctx:CwpParser.DiagramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by CwpParser#header.
    def visitHeader(self, ctx:CwpParser.HeaderContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by CwpParser#stateDecl.
    def visitStateDecl(self, ctx:CwpParser.StateDeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by CwpParser#edgeTransition.
    def visitEdgeTransition(self, ctx:CwpParser.EdgeTransitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by CwpParser#expr.
    def visitExpr(self, ctx:CwpParser.ExprContext):
        return self.visitChildren(ctx)



del CwpParser