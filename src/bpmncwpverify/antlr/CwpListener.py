# Generated from antlr/Cwp.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .CwpParser import CwpParser
else:
    from CwpParser import CwpParser

# This class defines a complete listener for a parse tree produced by CwpParser.
class CwpListener(ParseTreeListener):

    # Enter a parse tree produced by CwpParser#diagram.
    def enterDiagram(self, ctx:CwpParser.DiagramContext):
        pass

    # Exit a parse tree produced by CwpParser#diagram.
    def exitDiagram(self, ctx:CwpParser.DiagramContext):
        pass


    # Enter a parse tree produced by CwpParser#header.
    def enterHeader(self, ctx:CwpParser.HeaderContext):
        pass

    # Exit a parse tree produced by CwpParser#header.
    def exitHeader(self, ctx:CwpParser.HeaderContext):
        pass


    # Enter a parse tree produced by CwpParser#statesAndEdges.
    def enterStatesAndEdges(self, ctx:CwpParser.StatesAndEdgesContext):
        pass

    # Exit a parse tree produced by CwpParser#statesAndEdges.
    def exitStatesAndEdges(self, ctx:CwpParser.StatesAndEdgesContext):
        pass


    # Enter a parse tree produced by CwpParser#stateDecl.
    def enterStateDecl(self, ctx:CwpParser.StateDeclContext):
        pass

    # Exit a parse tree produced by CwpParser#stateDecl.
    def exitStateDecl(self, ctx:CwpParser.StateDeclContext):
        pass


    # Enter a parse tree produced by CwpParser#edgeTransition.
    def enterEdgeTransition(self, ctx:CwpParser.EdgeTransitionContext):
        pass

    # Exit a parse tree produced by CwpParser#edgeTransition.
    def exitEdgeTransition(self, ctx:CwpParser.EdgeTransitionContext):
        pass


    # Enter a parse tree produced by CwpParser#startTransition.
    def enterStartTransition(self, ctx:CwpParser.StartTransitionContext):
        pass

    # Exit a parse tree produced by CwpParser#startTransition.
    def exitStartTransition(self, ctx:CwpParser.StartTransitionContext):
        pass



del CwpParser