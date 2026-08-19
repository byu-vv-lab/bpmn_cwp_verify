# Generated from antlr/Cwp.g4 by ANTLR 4.13.2
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
        4,1,10,37,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,1,0,1,0,5,0,11,8,0,10,
        0,12,0,14,9,0,1,0,5,0,17,8,0,10,0,12,0,20,9,0,1,0,1,0,1,1,1,1,1,
        2,1,2,1,2,1,2,1,2,1,3,1,3,1,3,1,3,3,3,35,8,3,1,3,0,0,4,0,2,4,6,0,
        0,35,0,8,1,0,0,0,2,23,1,0,0,0,4,25,1,0,0,0,6,30,1,0,0,0,8,12,3,2,
        1,0,9,11,3,4,2,0,10,9,1,0,0,0,11,14,1,0,0,0,12,10,1,0,0,0,12,13,
        1,0,0,0,13,18,1,0,0,0,14,12,1,0,0,0,15,17,3,6,3,0,16,15,1,0,0,0,
        17,20,1,0,0,0,18,16,1,0,0,0,18,19,1,0,0,0,19,21,1,0,0,0,20,18,1,
        0,0,0,21,22,5,0,0,1,22,1,1,0,0,0,23,24,5,1,0,0,24,3,1,0,0,0,25,26,
        5,2,0,0,26,27,5,5,0,0,27,28,5,3,0,0,28,29,5,6,0,0,29,5,1,0,0,0,30,
        31,5,6,0,0,31,32,5,4,0,0,32,34,5,6,0,0,33,35,5,7,0,0,34,33,1,0,0,
        0,34,35,1,0,0,0,35,7,1,0,0,0,3,12,18,34
    ]

class CwpParser ( Parser ):

    grammarFileName = "Cwp.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'stateDiagram-v2'", "'state'", "'as'", 
                     "'-->'" ]

    symbolicNames = [ "<INVALID>", "STATEDIAGRAM", "STATE", "AS", "ARROW", 
                      "STRING", "ID", "EXPR_CLAUSE", "COMMENT", "WS", "NEWLINE" ]

    RULE_diagram = 0
    RULE_header = 1
    RULE_stateDecl = 2
    RULE_edgeTransition = 3

    ruleNames =  [ "diagram", "header", "stateDecl", "edgeTransition" ]

    EOF = Token.EOF
    STATEDIAGRAM=1
    STATE=2
    AS=3
    ARROW=4
    STRING=5
    ID=6
    EXPR_CLAUSE=7
    COMMENT=8
    WS=9
    NEWLINE=10

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




    def diagram(self):

        localctx = CwpParser.DiagramContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_diagram)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 8
            self.header()
            self.state = 12
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2:
                self.state = 9
                self.stateDecl()
                self.state = 14
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 18
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==6:
                self.state = 15
                self.edgeTransition()
                self.state = 20
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 21
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




    def header(self):

        localctx = CwpParser.HeaderContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_header)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 23
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




    def stateDecl(self):

        localctx = CwpParser.StateDeclContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_stateDecl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 25
            self.match(CwpParser.STATE)
            self.state = 26
            self.match(CwpParser.STRING)
            self.state = 27
            self.match(CwpParser.AS)
            self.state = 28
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

        def EXPR_CLAUSE(self):
            return self.getToken(CwpParser.EXPR_CLAUSE, 0)

        def getRuleIndex(self):
            return CwpParser.RULE_edgeTransition

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterEdgeTransition" ):
                listener.enterEdgeTransition(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitEdgeTransition" ):
                listener.exitEdgeTransition(self)




    def edgeTransition(self):

        localctx = CwpParser.EdgeTransitionContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_edgeTransition)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 30
            self.match(CwpParser.ID)
            self.state = 31
            self.match(CwpParser.ARROW)
            self.state = 32
            self.match(CwpParser.ID)
            self.state = 34
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==7:
                self.state = 33
                self.match(CwpParser.EXPR_CLAUSE)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





