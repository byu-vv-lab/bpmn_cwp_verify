# Generated from antlr/Expr.g4 by ANTLR 4.13.2
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
        4,1,21,114,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,1,0,1,0,1,0,1,1,1,1,1,2,1,2,
        1,2,1,2,1,2,1,2,5,2,34,8,2,10,2,12,2,37,9,2,1,3,1,3,1,3,1,3,1,3,
        1,3,5,3,45,8,3,10,3,12,3,48,9,3,1,4,1,4,1,4,3,4,53,8,4,1,5,1,5,1,
        5,1,5,1,5,1,5,5,5,61,8,5,10,5,12,5,64,9,5,1,6,1,6,1,6,1,6,1,6,1,
        6,5,6,72,8,6,10,6,12,6,75,9,6,1,7,1,7,1,7,1,7,1,7,1,7,5,7,83,8,7,
        10,7,12,7,86,9,7,1,8,1,8,1,8,3,8,91,8,8,1,9,1,9,1,9,1,9,1,9,1,9,
        1,9,4,9,100,8,9,11,9,12,9,101,1,9,3,9,105,8,9,1,10,1,10,1,10,1,10,
        1,10,3,10,112,8,10,1,10,0,5,4,6,10,12,14,11,0,2,4,6,8,10,12,14,16,
        18,20,0,3,1,0,4,9,1,0,10,11,1,0,12,14,113,0,22,1,0,0,0,2,25,1,0,
        0,0,4,27,1,0,0,0,6,38,1,0,0,0,8,52,1,0,0,0,10,54,1,0,0,0,12,65,1,
        0,0,0,14,76,1,0,0,0,16,90,1,0,0,0,18,104,1,0,0,0,20,111,1,0,0,0,
        22,23,3,2,1,0,23,24,5,0,0,1,24,1,1,0,0,0,25,26,3,4,2,0,26,3,1,0,
        0,0,27,28,6,2,-1,0,28,29,3,6,3,0,29,35,1,0,0,0,30,31,10,2,0,0,31,
        32,5,1,0,0,32,34,3,6,3,0,33,30,1,0,0,0,34,37,1,0,0,0,35,33,1,0,0,
        0,35,36,1,0,0,0,36,5,1,0,0,0,37,35,1,0,0,0,38,39,6,3,-1,0,39,40,
        3,8,4,0,40,46,1,0,0,0,41,42,10,2,0,0,42,43,5,2,0,0,43,45,3,8,4,0,
        44,41,1,0,0,0,45,48,1,0,0,0,46,44,1,0,0,0,46,47,1,0,0,0,47,7,1,0,
        0,0,48,46,1,0,0,0,49,50,5,3,0,0,50,53,3,8,4,0,51,53,3,10,5,0,52,
        49,1,0,0,0,52,51,1,0,0,0,53,9,1,0,0,0,54,55,6,5,-1,0,55,56,3,12,
        6,0,56,62,1,0,0,0,57,58,10,2,0,0,58,59,7,0,0,0,59,61,3,12,6,0,60,
        57,1,0,0,0,61,64,1,0,0,0,62,60,1,0,0,0,62,63,1,0,0,0,63,11,1,0,0,
        0,64,62,1,0,0,0,65,66,6,6,-1,0,66,67,3,14,7,0,67,73,1,0,0,0,68,69,
        10,2,0,0,69,70,7,1,0,0,70,72,3,14,7,0,71,68,1,0,0,0,72,75,1,0,0,
        0,73,71,1,0,0,0,73,74,1,0,0,0,74,13,1,0,0,0,75,73,1,0,0,0,76,77,
        6,7,-1,0,77,78,3,16,8,0,78,84,1,0,0,0,79,80,10,2,0,0,80,81,7,2,0,
        0,81,83,3,16,8,0,82,79,1,0,0,0,83,86,1,0,0,0,84,82,1,0,0,0,84,85,
        1,0,0,0,85,15,1,0,0,0,86,84,1,0,0,0,87,88,5,11,0,0,88,91,3,16,8,
        0,89,91,3,18,9,0,90,87,1,0,0,0,90,89,1,0,0,0,91,17,1,0,0,0,92,93,
        5,20,0,0,93,94,5,15,0,0,94,95,5,20,0,0,95,105,5,16,0,0,96,99,5,20,
        0,0,97,98,5,19,0,0,98,100,5,20,0,0,99,97,1,0,0,0,100,101,1,0,0,0,
        101,99,1,0,0,0,101,102,1,0,0,0,102,105,1,0,0,0,103,105,3,20,10,0,
        104,92,1,0,0,0,104,96,1,0,0,0,104,103,1,0,0,0,105,19,1,0,0,0,106,
        112,5,20,0,0,107,108,5,17,0,0,108,109,3,2,1,0,109,110,5,18,0,0,110,
        112,1,0,0,0,111,106,1,0,0,0,111,107,1,0,0,0,112,21,1,0,0,0,10,35,
        46,52,62,73,84,90,101,104,111
    ]

class ExprParser ( Parser ):

    grammarFileName = "Expr.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'||'", "'&&'", "'!'", "'<'", "'<='", 
                     "'=='", "'!='", "'>'", "'>='", "'+'", "'-'", "'*'", 
                     "'/'", "'%'", "'['", "']'", "'('", "')'", "'.'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "PERIOD", "ID", 
                      "WS" ]

    RULE_start = 0
    RULE_expr = 1
    RULE_orExpr = 2
    RULE_andExpr = 3
    RULE_notExpr = 4
    RULE_relExpr = 5
    RULE_addSubExpr = 6
    RULE_mulDivExpr = 7
    RULE_unaryExpr = 8
    RULE_postfixExpr = 9
    RULE_atom = 10

    ruleNames =  [ "start", "expr", "orExpr", "andExpr", "notExpr", "relExpr", 
                   "addSubExpr", "mulDivExpr", "unaryExpr", "postfixExpr", 
                   "atom" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    T__10=11
    T__11=12
    T__12=13
    T__13=14
    T__14=15
    T__15=16
    T__16=17
    T__17=18
    PERIOD=19
    ID=20
    WS=21

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StartContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def expr(self):
            return self.getTypedRuleContext(ExprParser.ExprContext,0)


        def EOF(self):
            return self.getToken(ExprParser.EOF, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_start

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStart" ):
                listener.enterStart(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStart" ):
                listener.exitStart(self)




    def start(self):

        localctx = ExprParser.StartContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_start)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 22
            self.expr()
            self.state = 23
            self.match(ExprParser.EOF)
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

        def orExpr(self):
            return self.getTypedRuleContext(ExprParser.OrExprContext,0)


        def getRuleIndex(self):
            return ExprParser.RULE_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExpr" ):
                listener.enterExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExpr" ):
                listener.exitExpr(self)




    def expr(self):

        localctx = ExprParser.ExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 25
            self.orExpr(0)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class OrExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_orExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class OrContext(OrExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.OrExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def orExpr(self):
            return self.getTypedRuleContext(ExprParser.OrExprContext,0)

        def andExpr(self):
            return self.getTypedRuleContext(ExprParser.AndExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterOr" ):
                listener.enterOr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitOr" ):
                listener.exitOr(self)


    class ToAndContext(OrExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.OrExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def andExpr(self):
            return self.getTypedRuleContext(ExprParser.AndExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToAnd" ):
                listener.enterToAnd(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToAnd" ):
                listener.exitToAnd(self)



    def orExpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.OrExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 4
        self.enterRecursionRule(localctx, 4, self.RULE_orExpr, _p)
        try:
            self.enterOuterAlt(localctx, 1)
            localctx = ExprParser.ToAndContext(self, localctx)
            self._ctx = localctx
            _prevctx = localctx

            self.state = 28
            self.andExpr(0)
            self._ctx.stop = self._input.LT(-1)
            self.state = 35
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,0,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.OrContext(self, ExprParser.OrExprContext(self, _parentctx, _parentState))
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_orExpr)
                    self.state = 30
                    if not self.precpred(self._ctx, 2):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                    self.state = 31
                    self.match(ExprParser.T__0)
                    self.state = 32
                    self.andExpr(0) 
                self.state = 37
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,0,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class AndExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_andExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class AndContext(AndExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.AndExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def andExpr(self):
            return self.getTypedRuleContext(ExprParser.AndExprContext,0)

        def notExpr(self):
            return self.getTypedRuleContext(ExprParser.NotExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAnd" ):
                listener.enterAnd(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAnd" ):
                listener.exitAnd(self)


    class ToNotContext(AndExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.AndExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def notExpr(self):
            return self.getTypedRuleContext(ExprParser.NotExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToNot" ):
                listener.enterToNot(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToNot" ):
                listener.exitToNot(self)



    def andExpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.AndExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 6
        self.enterRecursionRule(localctx, 6, self.RULE_andExpr, _p)
        try:
            self.enterOuterAlt(localctx, 1)
            localctx = ExprParser.ToNotContext(self, localctx)
            self._ctx = localctx
            _prevctx = localctx

            self.state = 39
            self.notExpr()
            self._ctx.stop = self._input.LT(-1)
            self.state = 46
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,1,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.AndContext(self, ExprParser.AndExprContext(self, _parentctx, _parentState))
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_andExpr)
                    self.state = 41
                    if not self.precpred(self._ctx, 2):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                    self.state = 42
                    self.match(ExprParser.T__1)
                    self.state = 43
                    self.notExpr() 
                self.state = 48
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,1,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class NotExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_notExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class NotContext(NotExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.NotExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def notExpr(self):
            return self.getTypedRuleContext(ExprParser.NotExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNot" ):
                listener.enterNot(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNot" ):
                listener.exitNot(self)


    class ToRelContext(NotExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.NotExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def relExpr(self):
            return self.getTypedRuleContext(ExprParser.RelExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToRel" ):
                listener.enterToRel(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToRel" ):
                listener.exitToRel(self)



    def notExpr(self):

        localctx = ExprParser.NotExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_notExpr)
        try:
            self.state = 52
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [3]:
                localctx = ExprParser.NotContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 49
                self.match(ExprParser.T__2)
                self.state = 50
                self.notExpr()
                pass
            elif token in [11, 17, 20]:
                localctx = ExprParser.ToRelContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 51
                self.relExpr(0)
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


    class RelExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_relExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class RelationalContext(RelExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.RelExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def relExpr(self):
            return self.getTypedRuleContext(ExprParser.RelExprContext,0)

        def addSubExpr(self):
            return self.getTypedRuleContext(ExprParser.AddSubExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterRelational" ):
                listener.enterRelational(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitRelational" ):
                listener.exitRelational(self)


    class ToAddSubContext(RelExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.RelExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def addSubExpr(self):
            return self.getTypedRuleContext(ExprParser.AddSubExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToAddSub" ):
                listener.enterToAddSub(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToAddSub" ):
                listener.exitToAddSub(self)



    def relExpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.RelExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 10
        self.enterRecursionRule(localctx, 10, self.RULE_relExpr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            localctx = ExprParser.ToAddSubContext(self, localctx)
            self._ctx = localctx
            _prevctx = localctx

            self.state = 55
            self.addSubExpr(0)
            self._ctx.stop = self._input.LT(-1)
            self.state = 62
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,3,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.RelationalContext(self, ExprParser.RelExprContext(self, _parentctx, _parentState))
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_relExpr)
                    self.state = 57
                    if not self.precpred(self._ctx, 2):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                    self.state = 58
                    localctx.op = self._input.LT(1)
                    _la = self._input.LA(1)
                    if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 1008) != 0)):
                        localctx.op = self._errHandler.recoverInline(self)
                    else:
                        self._errHandler.reportMatch(self)
                        self.consume()
                    self.state = 59
                    self.addSubExpr(0) 
                self.state = 64
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,3,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class AddSubExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_addSubExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class AddSubContext(AddSubExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.AddSubExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def addSubExpr(self):
            return self.getTypedRuleContext(ExprParser.AddSubExprContext,0)

        def mulDivExpr(self):
            return self.getTypedRuleContext(ExprParser.MulDivExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAddSub" ):
                listener.enterAddSub(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAddSub" ):
                listener.exitAddSub(self)


    class ToMulDivContext(AddSubExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.AddSubExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def mulDivExpr(self):
            return self.getTypedRuleContext(ExprParser.MulDivExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToMulDiv" ):
                listener.enterToMulDiv(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToMulDiv" ):
                listener.exitToMulDiv(self)



    def addSubExpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.AddSubExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 12
        self.enterRecursionRule(localctx, 12, self.RULE_addSubExpr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            localctx = ExprParser.ToMulDivContext(self, localctx)
            self._ctx = localctx
            _prevctx = localctx

            self.state = 66
            self.mulDivExpr(0)
            self._ctx.stop = self._input.LT(-1)
            self.state = 73
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,4,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.AddSubContext(self, ExprParser.AddSubExprContext(self, _parentctx, _parentState))
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_addSubExpr)
                    self.state = 68
                    if not self.precpred(self._ctx, 2):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                    self.state = 69
                    localctx.op = self._input.LT(1)
                    _la = self._input.LA(1)
                    if not(_la==10 or _la==11):
                        localctx.op = self._errHandler.recoverInline(self)
                    else:
                        self._errHandler.reportMatch(self)
                        self.consume()
                    self.state = 70
                    self.mulDivExpr(0) 
                self.state = 75
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,4,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class MulDivExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_mulDivExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class ToUnaryContext(MulDivExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.MulDivExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def unaryExpr(self):
            return self.getTypedRuleContext(ExprParser.UnaryExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToUnary" ):
                listener.enterToUnary(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToUnary" ):
                listener.exitToUnary(self)


    class MulDivContext(MulDivExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.MulDivExprContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def mulDivExpr(self):
            return self.getTypedRuleContext(ExprParser.MulDivExprContext,0)

        def unaryExpr(self):
            return self.getTypedRuleContext(ExprParser.UnaryExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMulDiv" ):
                listener.enterMulDiv(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMulDiv" ):
                listener.exitMulDiv(self)



    def mulDivExpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.MulDivExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 14
        self.enterRecursionRule(localctx, 14, self.RULE_mulDivExpr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            localctx = ExprParser.ToUnaryContext(self, localctx)
            self._ctx = localctx
            _prevctx = localctx

            self.state = 77
            self.unaryExpr()
            self._ctx.stop = self._input.LT(-1)
            self.state = 84
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,5,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.MulDivContext(self, ExprParser.MulDivExprContext(self, _parentctx, _parentState))
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_mulDivExpr)
                    self.state = 79
                    if not self.precpred(self._ctx, 2):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                    self.state = 80
                    localctx.op = self._input.LT(1)
                    _la = self._input.LA(1)
                    if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 28672) != 0)):
                        localctx.op = self._errHandler.recoverInline(self)
                    else:
                        self._errHandler.reportMatch(self)
                        self.consume()
                    self.state = 81
                    self.unaryExpr() 
                self.state = 86
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,5,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class UnaryExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_unaryExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class ToPostfixContext(UnaryExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.UnaryExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def postfixExpr(self):
            return self.getTypedRuleContext(ExprParser.PostfixExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToPostfix" ):
                listener.enterToPostfix(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToPostfix" ):
                listener.exitToPostfix(self)


    class NegateContext(UnaryExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.UnaryExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def unaryExpr(self):
            return self.getTypedRuleContext(ExprParser.UnaryExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNegate" ):
                listener.enterNegate(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNegate" ):
                listener.exitNegate(self)



    def unaryExpr(self):

        localctx = ExprParser.UnaryExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_unaryExpr)
        try:
            self.state = 90
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [11]:
                localctx = ExprParser.NegateContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 87
                self.match(ExprParser.T__10)
                self.state = 88
                self.unaryExpr()
                pass
            elif token in [17, 20]:
                localctx = ExprParser.ToPostfixContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 89
                self.postfixExpr()
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


    class PostfixExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_postfixExpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class ArrayAccessContext(PostfixExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.PostfixExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterArrayAccess" ):
                listener.enterArrayAccess(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitArrayAccess" ):
                listener.exitArrayAccess(self)


    class FieldAccessContext(PostfixExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.PostfixExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)
        def PERIOD(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.PERIOD)
            else:
                return self.getToken(ExprParser.PERIOD, i)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterFieldAccess" ):
                listener.enterFieldAccess(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitFieldAccess" ):
                listener.exitFieldAccess(self)


    class ToAtomContext(PostfixExprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.PostfixExprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def atom(self):
            return self.getTypedRuleContext(ExprParser.AtomContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterToAtom" ):
                listener.enterToAtom(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitToAtom" ):
                listener.exitToAtom(self)



    def postfixExpr(self):

        localctx = ExprParser.PostfixExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 18, self.RULE_postfixExpr)
        try:
            self.state = 104
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,8,self._ctx)
            if la_ == 1:
                localctx = ExprParser.ArrayAccessContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 92
                self.match(ExprParser.ID)
                self.state = 93
                self.match(ExprParser.T__14)
                self.state = 94
                self.match(ExprParser.ID)
                self.state = 95
                self.match(ExprParser.T__15)
                pass

            elif la_ == 2:
                localctx = ExprParser.FieldAccessContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 96
                self.match(ExprParser.ID)
                self.state = 99 
                self._errHandler.sync(self)
                _alt = 1
                while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                    if _alt == 1:
                        self.state = 97
                        self.match(ExprParser.PERIOD)
                        self.state = 98
                        self.match(ExprParser.ID)

                    else:
                        raise NoViableAltException(self)
                    self.state = 101 
                    self._errHandler.sync(self)
                    _alt = self._interp.adaptivePredict(self._input,7,self._ctx)

                pass

            elif la_ == 3:
                localctx = ExprParser.ToAtomContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 103
                self.atom()
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class AtomContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ExprParser.RULE_atom

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)



    class ParensContext(AtomContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.AtomContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def expr(self):
            return self.getTypedRuleContext(ExprParser.ExprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterParens" ):
                listener.enterParens(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitParens" ):
                listener.exitParens(self)


    class IDContext(AtomContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ExprParser.AtomContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(ExprParser.ID, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterID" ):
                listener.enterID(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitID" ):
                listener.exitID(self)



    def atom(self):

        localctx = ExprParser.AtomContext(self, self._ctx, self.state)
        self.enterRule(localctx, 20, self.RULE_atom)
        try:
            self.state = 111
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [20]:
                localctx = ExprParser.IDContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 106
                self.match(ExprParser.ID)
                pass
            elif token in [17]:
                localctx = ExprParser.ParensContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 107
                self.match(ExprParser.T__16)
                self.state = 108
                self.expr()
                self.state = 109
                self.match(ExprParser.T__17)
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



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[2] = self.orExpr_sempred
        self._predicates[3] = self.andExpr_sempred
        self._predicates[5] = self.relExpr_sempred
        self._predicates[6] = self.addSubExpr_sempred
        self._predicates[7] = self.mulDivExpr_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def orExpr_sempred(self, localctx:OrExprContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 2)
         

    def andExpr_sempred(self, localctx:AndExprContext, predIndex:int):
            if predIndex == 1:
                return self.precpred(self._ctx, 2)
         

    def relExpr_sempred(self, localctx:RelExprContext, predIndex:int):
            if predIndex == 2:
                return self.precpred(self._ctx, 2)
         

    def addSubExpr_sempred(self, localctx:AddSubExprContext, predIndex:int):
            if predIndex == 3:
                return self.precpred(self._ctx, 2)
         

    def mulDivExpr_sempred(self, localctx:MulDivExprContext, predIndex:int):
            if predIndex == 4:
                return self.precpred(self._ctx, 2)
         




