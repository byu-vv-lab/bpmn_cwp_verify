# Generated from antlr/CwpParser.g4 by ANTLR 4.13.2
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,12,42,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,1,0,5,0,13,
        8,0,10,0,12,0,16,9,0,1,0,5,0,19,8,0,10,0,12,0,22,9,0,1,0,1,0,1,1,
        1,1,1,2,1,2,1,2,1,2,1,2,1,3,1,3,1,3,1,3,1,3,3,3,38,8,3,1,4,1,4,1,
        4,0,0,5,0,2,4,6,8,0,0,39,0,10,1,0,0,0,2,25,1,0,0,0,4,27,1,0,0,0,
        6,32,1,0,0,0,8,39,1,0,0,0,10,14,3,2,1,0,11,13,3,4,2,0,12,11,1,0,
        0,0,13,16,1,0,0,0,14,12,1,0,0,0,14,15,1,0,0,0,15,20,1,0,0,0,16,14,
        1,0,0,0,17,19,3,6,3,0,18,17,1,0,0,0,19,22,1,0,0,0,20,18,1,0,0,0,
        20,21,1,0,0,0,21,23,1,0,0,0,22,20,1,0,0,0,23,24,5,0,0,1,24,1,1,0,
        0,0,25,26,5,1,0,0,26,3,1,0,0,0,27,28,5,2,0,0,28,29,5,6,0,0,29,30,
        5,3,0,0,30,31,5,7,0,0,31,5,1,0,0,0,32,33,5,7,0,0,33,34,5,4,0,0,34,
        37,5,7,0,0,35,36,5,5,0,0,36,38,3,8,4,0,37,35,1,0,0,0,37,38,1,0,0,
        0,38,7,1,0,0,0,39,40,5,11,0,0,40,9,1,0,0,0,3,14,20,37
    ]

class CwpParser ( Parser ):

    grammarFileName = "CwpParser.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'stateDiagram-v2'", "'state'", "'as'", 
                     "'-->'", "':'" ]

    symbolicNames = [ "<INVALID>", "STATEDIAGRAM", "STATE", "AS", "ARROW", 
                      "COLON", "STRING", "ID", "COMMENT", "WS", "NEWLINE", 
                      "EXPR_TEXT", "EXPR_NL" ]

    RULE_diagram = 0
    RULE_header = 1
    RULE_stateDecl = 2
    RULE_edgeTransition = 3
    RULE_expr = 4

    ruleNames =  [ "diagram", "header", "stateDecl", "edgeTransition", "expr" ]

    EOF = Token.EOF
    STATEDIAGRAM=1
    STATE=2
    AS=3
    ARROW=4
    COLON=5
    STRING=6
    ID=7
    COMMENT=8
    WS=9
    NEWLINE=10
    EXPR_TEXT=11
    EXPR_NL=12

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class DiagramContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def header(self):
            return self.getTypedRuleContext(CwpParser.HeaderContext,0)


        def EOF(self):
            return self.getToken(CwpParser.EOF, 0)

        def stateDecl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CwpParser.StateDeclContext)
            else:
                return self.getTypedRuleContext(CwpParser.StateDeclContext,i)


        def edgeTransition(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CwpParser.EdgeTransitionContext)
            else:
                return self.getTypedRuleContext(CwpParser.EdgeTransitionContext,i)


        def getRuleIndex(self):
            return CwpParser.RULE_diagram

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterDiagram" ):
                listener.enterDiagram(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitDiagram" ):
                listener.exitDiagram(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitDiagram" ):
                return visitor.visitDiagram(self)
            else:
                return visitor.visitChildren(self)




    def diagram(self):

        localctx = CwpParser.DiagramContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_diagram)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 10
            self.header()
            self.state = 14
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2:
                self.state = 11
                self.stateDecl()
                self.state = 16
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 20
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==7:
                self.state = 17
                self.edgeTransition()
                self.state = 22
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 23
            self.match(CwpParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class HeaderContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def STATEDIAGRAM(self):
            return self.getToken(CwpParser.STATEDIAGRAM, 0)

        def getRuleIndex(self):
            return CwpParser.RULE_header

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterHeader" ):
                listener.enterHeader(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitHeader" ):
                listener.exitHeader(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitHeader" ):
                return visitor.visitHeader(self)
            else:
                return visitor.visitChildren(self)




    def header(self):

        localctx = CwpParser.HeaderContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_header)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 25
            self.match(CwpParser.STATEDIAGRAM)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StateDeclContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def STATE(self):
            return self.getToken(CwpParser.STATE, 0)

        def STRING(self):
            return self.getToken(CwpParser.STRING, 0)

        def AS(self):
            return self.getToken(CwpParser.AS, 0)

        def ID(self):
            return self.getToken(CwpParser.ID, 0)

        def getRuleIndex(self):
            return CwpParser.RULE_stateDecl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStateDecl" ):
                listener.enterStateDecl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStateDecl" ):
                listener.exitStateDecl(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStateDecl" ):
                return visitor.visitStateDecl(self)
            else:
                return visitor.visitChildren(self)




    def stateDecl(self):

        localctx = CwpParser.StateDeclContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_stateDecl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 27
            self.match(CwpParser.STATE)
            self.state = 28
            self.match(CwpParser.STRING)
            self.state = 29
            self.match(CwpParser.AS)
            self.state = 30
            self.match(CwpParser.ID)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class EdgeTransitionContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(CwpParser.ID)
            else:
                return self.getToken(CwpParser.ID, i)

        def ARROW(self):
            return self.getToken(CwpParser.ARROW, 0)

        def COLON(self):
            return self.getToken(CwpParser.COLON, 0)

        def expr(self):
            return self.getTypedRuleContext(CwpParser.ExprContext,0)


        def getRuleIndex(self):
            return CwpParser.RULE_edgeTransition

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterEdgeTransition" ):
                listener.enterEdgeTransition(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitEdgeTransition" ):
                listener.exitEdgeTransition(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitEdgeTransition" ):
                return visitor.visitEdgeTransition(self)
            else:
                return visitor.visitChildren(self)




    def edgeTransition(self):

        localctx = CwpParser.EdgeTransitionContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_edgeTransition)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 32
            self.match(CwpParser.ID)
            self.state = 33
            self.match(CwpParser.ARROW)
            self.state = 34
            self.match(CwpParser.ID)
            self.state = 37
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==5:
                self.state = 35
                self.match(CwpParser.COLON)
                self.state = 36
                self.expr()


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def EXPR_TEXT(self):
            return self.getToken(CwpParser.EXPR_TEXT, 0)

        def getRuleIndex(self):
            return CwpParser.RULE_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExpr" ):
                listener.enterExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExpr" ):
                listener.exitExpr(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitExpr" ):
                return visitor.visitExpr(self)
            else:
                return visitor.visitChildren(self)




    def expr(self):

        localctx = CwpParser.ExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 39
            self.match(CwpParser.EXPR_TEXT)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





