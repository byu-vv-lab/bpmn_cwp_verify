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
        4,1,11,52,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,1,0,1,
        0,5,0,15,8,0,10,0,12,0,18,9,0,1,0,1,0,5,0,22,8,0,10,0,12,0,25,9,
        0,1,0,1,0,1,1,1,1,1,2,1,2,3,2,33,8,2,1,3,1,3,1,3,1,3,1,3,1,4,1,4,
        1,4,1,4,3,4,44,8,4,1,5,1,5,1,5,1,5,3,5,50,8,5,1,5,0,0,6,0,2,4,6,
        8,10,0,0,50,0,12,1,0,0,0,2,28,1,0,0,0,4,32,1,0,0,0,6,34,1,0,0,0,
        8,39,1,0,0,0,10,45,1,0,0,0,12,16,3,2,1,0,13,15,3,4,2,0,14,13,1,0,
        0,0,15,18,1,0,0,0,16,14,1,0,0,0,16,17,1,0,0,0,17,19,1,0,0,0,18,16,
        1,0,0,0,19,23,3,10,5,0,20,22,3,4,2,0,21,20,1,0,0,0,22,25,1,0,0,0,
        23,21,1,0,0,0,23,24,1,0,0,0,24,26,1,0,0,0,25,23,1,0,0,0,26,27,5,
        0,0,1,27,1,1,0,0,0,28,29,5,1,0,0,29,3,1,0,0,0,30,33,3,6,3,0,31,33,
        3,8,4,0,32,30,1,0,0,0,32,31,1,0,0,0,33,5,1,0,0,0,34,35,5,2,0,0,35,
        36,5,6,0,0,36,37,5,3,0,0,37,38,5,7,0,0,38,7,1,0,0,0,39,40,5,7,0,
        0,40,41,5,5,0,0,41,43,5,7,0,0,42,44,5,8,0,0,43,42,1,0,0,0,43,44,
        1,0,0,0,44,9,1,0,0,0,45,46,5,4,0,0,46,47,5,5,0,0,47,49,5,7,0,0,48,
        50,5,8,0,0,49,48,1,0,0,0,49,50,1,0,0,0,50,11,1,0,0,0,5,16,23,32,
        43,49
    ]

class CwpParser ( Parser ):

    grammarFileName = "Cwp.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'stateDiagram-v2'", "'state'", "'as'", 
                     "'[*]'", "'-->'" ]

    symbolicNames = [ "<INVALID>", "STATEDIAGRAM", "STATE", "AS", "START", 
                      "ARROW", "STRING", "ID", "EXPR_CLAUSE", "COMMENT", 
                      "WS", "NEWLINE" ]

    RULE_diagram = 0
    RULE_header = 1
    RULE_statesAndEdges = 2
    RULE_stateDecl = 3
    RULE_edgeTransition = 4
    RULE_startTransition = 5

    ruleNames =  [ "diagram", "header", "statesAndEdges", "stateDecl", "edgeTransition", 
                   "startTransition" ]

    EOF = Token.EOF
    STATEDIAGRAM=1
    STATE=2
    AS=3
    START=4
    ARROW=5
    STRING=6
    ID=7
    EXPR_CLAUSE=8
    COMMENT=9
    WS=10
    NEWLINE=11

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


        def startTransition(self):
            return self.getTypedRuleContext(CwpParser.StartTransitionContext,0)


        def EOF(self):
            return self.getToken(CwpParser.EOF, 0)

        def statesAndEdges(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(CwpParser.StatesAndEdgesContext)
            else:
                return self.getTypedRuleContext(CwpParser.StatesAndEdgesContext,i)


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
            self.state = 12
            self.header()
            self.state = 16
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2 or _la==7:
                self.state = 13
                self.statesAndEdges()
                self.state = 18
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 19
            self.startTransition()
            self.state = 23
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2 or _la==7:
                self.state = 20
                self.statesAndEdges()
                self.state = 25
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 26
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
            self.state = 28
            self.match(CwpParser.STATEDIAGRAM)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StatesAndEdgesContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def stateDecl(self):
            return self.getTypedRuleContext(CwpParser.StateDeclContext,0)


        def edgeTransition(self):
            return self.getTypedRuleContext(CwpParser.EdgeTransitionContext,0)


        def getRuleIndex(self):
            return CwpParser.RULE_statesAndEdges

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStatesAndEdges" ):
                listener.enterStatesAndEdges(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStatesAndEdges" ):
                listener.exitStatesAndEdges(self)




    def statesAndEdges(self):

        localctx = CwpParser.StatesAndEdgesContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_statesAndEdges)
        try:
            self.state = 32
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [2]:
                self.enterOuterAlt(localctx, 1)
                self.state = 30
                self.stateDecl()
                pass
            elif token in [7]:
                self.enterOuterAlt(localctx, 2)
                self.state = 31
                self.edgeTransition()
                pass
            else:
                raise NoViableAltException(self)

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
        self.enterRule(localctx, 6, self.RULE_stateDecl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 34
            self.match(CwpParser.STATE)
            self.state = 35
            self.match(CwpParser.STRING)
            self.state = 36
            self.match(CwpParser.AS)
            self.state = 37
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
        self.enterRule(localctx, 8, self.RULE_edgeTransition)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 39
            self.match(CwpParser.ID)
            self.state = 40
            self.match(CwpParser.ARROW)
            self.state = 41
            self.match(CwpParser.ID)
            self.state = 43
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==8:
                self.state = 42
                self.match(CwpParser.EXPR_CLAUSE)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class StartTransitionContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def START(self):
            return self.getToken(CwpParser.START, 0)

        def ARROW(self):
            return self.getToken(CwpParser.ARROW, 0)

        def ID(self):
            return self.getToken(CwpParser.ID, 0)

        def EXPR_CLAUSE(self):
            return self.getToken(CwpParser.EXPR_CLAUSE, 0)

        def getRuleIndex(self):
            return CwpParser.RULE_startTransition

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStartTransition" ):
                listener.enterStartTransition(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStartTransition" ):
                listener.exitStartTransition(self)




    def startTransition(self):

        localctx = CwpParser.StartTransitionContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_startTransition)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 45
            self.match(CwpParser.START)
            self.state = 46
            self.match(CwpParser.ARROW)
            self.state = 47
            self.match(CwpParser.ID)
            self.state = 49
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==8:
                self.state = 48
                self.match(CwpParser.EXPR_CLAUSE)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





