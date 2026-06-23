# Generated from ./Desktop/bpmn_cwp_verify/antlr/State.g4 by ANTLR 4.13.2
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
        4,1,18,104,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,1,0,5,0,20,8,0,10,0,12,0,23,9,0,1,0,5,0,26,8,0,
        10,0,12,0,29,9,0,1,0,5,0,32,8,0,10,0,12,0,35,9,0,1,0,4,0,38,8,0,
        11,0,12,0,39,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,4,2,51,8,2,11,2,
        12,2,52,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,
        1,4,1,4,1,4,3,4,72,8,4,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,
        5,1,5,1,6,4,6,87,8,6,11,6,12,6,88,1,6,1,6,5,6,93,8,6,10,6,12,6,96,
        9,6,1,7,1,7,3,7,100,8,7,1,8,1,8,1,8,0,0,9,0,2,4,6,8,10,12,14,16,
        0,1,2,0,3,5,8,9,103,0,21,1,0,0,0,2,43,1,0,0,0,4,50,1,0,0,0,6,54,
        1,0,0,0,8,61,1,0,0,0,10,73,1,0,0,0,12,86,1,0,0,0,14,99,1,0,0,0,16,
        101,1,0,0,0,18,20,3,2,1,0,19,18,1,0,0,0,20,23,1,0,0,0,21,19,1,0,
        0,0,21,22,1,0,0,0,22,27,1,0,0,0,23,21,1,0,0,0,24,26,3,6,3,0,25,24,
        1,0,0,0,26,29,1,0,0,0,27,25,1,0,0,0,27,28,1,0,0,0,28,33,1,0,0,0,
        29,27,1,0,0,0,30,32,3,10,5,0,31,30,1,0,0,0,32,35,1,0,0,0,33,31,1,
        0,0,0,33,34,1,0,0,0,34,37,1,0,0,0,35,33,1,0,0,0,36,38,3,8,4,0,37,
        36,1,0,0,0,38,39,1,0,0,0,39,37,1,0,0,0,39,40,1,0,0,0,40,41,1,0,0,
        0,41,42,5,0,0,1,42,1,1,0,0,0,43,44,5,7,0,0,44,45,5,16,0,0,45,46,
        5,11,0,0,46,47,3,4,2,0,47,48,5,12,0,0,48,3,1,0,0,0,49,51,5,16,0,
        0,50,49,1,0,0,0,51,52,1,0,0,0,52,50,1,0,0,0,52,53,1,0,0,0,53,5,1,
        0,0,0,54,55,5,6,0,0,55,56,5,16,0,0,56,57,5,1,0,0,57,58,3,14,7,0,
        58,59,5,10,0,0,59,60,5,16,0,0,60,7,1,0,0,0,61,62,5,15,0,0,62,63,
        5,16,0,0,63,64,5,1,0,0,64,65,3,14,7,0,65,66,5,10,0,0,66,71,5,16,
        0,0,67,68,5,11,0,0,68,69,3,4,2,0,69,70,5,12,0,0,70,72,1,0,0,0,71,
        67,1,0,0,0,71,72,1,0,0,0,72,9,1,0,0,0,73,74,5,15,0,0,74,75,5,16,
        0,0,75,76,5,1,0,0,76,77,3,14,7,0,77,78,5,13,0,0,78,79,5,17,0,0,79,
        80,5,14,0,0,80,81,5,10,0,0,81,82,5,13,0,0,82,83,3,12,6,0,83,84,5,
        14,0,0,84,11,1,0,0,0,85,87,5,16,0,0,86,85,1,0,0,0,87,88,1,0,0,0,
        88,86,1,0,0,0,88,89,1,0,0,0,89,94,1,0,0,0,90,91,5,2,0,0,91,93,5,
        16,0,0,92,90,1,0,0,0,93,96,1,0,0,0,94,92,1,0,0,0,94,95,1,0,0,0,95,
        13,1,0,0,0,96,94,1,0,0,0,97,100,3,16,8,0,98,100,5,16,0,0,99,97,1,
        0,0,0,99,98,1,0,0,0,100,15,1,0,0,0,101,102,7,0,0,0,102,17,1,0,0,
        0,9,21,27,33,39,52,71,88,94,99
    ]

class StateParser ( Parser ):

    grammarFileName = "State.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "','", "'bit'", "'bool'", "'byte'", 
                     "'const'", "'enum'", "'int'", "'short'", "'='", "'{'", 
                     "'}'", "'['", "']'", "'var'" ]

    symbolicNames = [ "<INVALID>", "COLON", "COMMA", "BIT", "BOOL", "BYTE", 
                      "CONST", "ENUM", "INT", "SHORT", "EQUALS", "LCURLY", 
                      "RCURLY", "LBRACKET", "RBRACKET", "VAR", "ID", "NUMBER", 
                      "WS" ]

    RULE_state = 0
    RULE_enum_type_decl = 1
    RULE_id_set = 2
    RULE_const_var_decl = 3
    RULE_var_decl = 4
    RULE_array_decl = 5
    RULE_id_list = 6
    RULE_type = 7
    RULE_primitive_type = 8

    ruleNames =  [ "state", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl", "array_decl", "id_list", "type", "primitive_type" ]

    EOF = Token.EOF
    COLON=1
    COMMA=2
    BIT=3
    BOOL=4
    BYTE=5
    CONST=6
    ENUM=7
    INT=8
    SHORT=9
    EQUALS=10
    LCURLY=11
    RCURLY=12
    LBRACKET=13
    RBRACKET=14
    VAR=15
    ID=16
    NUMBER=17
    WS=18

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StateContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def EOF(self):
            return self.getToken(StateParser.EOF, 0)

        def enum_type_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Enum_type_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Enum_type_declContext,i)


        def const_var_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Const_var_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Const_var_declContext,i)


        def array_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Array_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Array_declContext,i)


        def var_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Var_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Var_declContext,i)


        def getRuleIndex(self):
            return StateParser.RULE_state

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterState" ):
                listener.enterState(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitState" ):
                listener.exitState(self)




    def state_(self):

        localctx = StateParser.StateContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_state)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 21
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==7:
                self.state = 18
                self.enum_type_decl()
                self.state = 23
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 27
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==6:
                self.state = 24
                self.const_var_decl()
                self.state = 29
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 33
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,2,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 30
                    self.array_decl() 
                self.state = 35
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,2,self._ctx)

            self.state = 37 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 36
                self.var_decl()
                self.state = 39 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==15):
                    break

            self.state = 41
            self.match(StateParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Enum_type_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ENUM(self):
            return self.getToken(StateParser.ENUM, 0)

        def ID(self):
            return self.getToken(StateParser.ID, 0)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def id_set(self):
            return self.getTypedRuleContext(StateParser.Id_setContext,0)


        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateParser.RULE_enum_type_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterEnum_type_decl" ):
                listener.enterEnum_type_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitEnum_type_decl" ):
                listener.exitEnum_type_decl(self)




    def enum_type_decl(self):

        localctx = StateParser.Enum_type_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_enum_type_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 43
            self.match(StateParser.ENUM)
            self.state = 44
            self.match(StateParser.ID)
            self.state = 45
            self.match(StateParser.LCURLY)
            self.state = 46
            self.id_set()
            self.state = 47
            self.match(StateParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Id_setContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def getRuleIndex(self):
            return StateParser.RULE_id_set

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterId_set" ):
                listener.enterId_set(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitId_set" ):
                listener.exitId_set(self)




    def id_set(self):

        localctx = StateParser.Id_setContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_id_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 50 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 49
                self.match(StateParser.ID)
                self.state = 52 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==16):
                    break

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Const_var_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def CONST(self):
            return self.getToken(StateParser.CONST, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def COLON(self):
            return self.getToken(StateParser.COLON, 0)

        def type_(self):
            return self.getTypedRuleContext(StateParser.TypeContext,0)


        def EQUALS(self):
            return self.getToken(StateParser.EQUALS, 0)

        def getRuleIndex(self):
            return StateParser.RULE_const_var_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterConst_var_decl" ):
                listener.enterConst_var_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitConst_var_decl" ):
                listener.exitConst_var_decl(self)




    def const_var_decl(self):

        localctx = StateParser.Const_var_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_const_var_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 54
            self.match(StateParser.CONST)
            self.state = 55
            self.match(StateParser.ID)
            self.state = 56
            self.match(StateParser.COLON)
            self.state = 57
            self.type_()
            self.state = 58
            self.match(StateParser.EQUALS)
            self.state = 59
            self.match(StateParser.ID)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Var_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def VAR(self):
            return self.getToken(StateParser.VAR, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def COLON(self):
            return self.getToken(StateParser.COLON, 0)

        def type_(self):
            return self.getTypedRuleContext(StateParser.TypeContext,0)


        def EQUALS(self):
            return self.getToken(StateParser.EQUALS, 0)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def id_set(self):
            return self.getTypedRuleContext(StateParser.Id_setContext,0)


        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateParser.RULE_var_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterVar_decl" ):
                listener.enterVar_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitVar_decl" ):
                listener.exitVar_decl(self)




    def var_decl(self):

        localctx = StateParser.Var_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_var_decl)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 61
            self.match(StateParser.VAR)
            self.state = 62
            self.match(StateParser.ID)
            self.state = 63
            self.match(StateParser.COLON)
            self.state = 64
            self.type_()
            self.state = 65
            self.match(StateParser.EQUALS)
            self.state = 66
            self.match(StateParser.ID)
            self.state = 71
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==11:
                self.state = 67
                self.match(StateParser.LCURLY)
                self.state = 68
                self.id_set()
                self.state = 69
                self.match(StateParser.RCURLY)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Array_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def VAR(self):
            return self.getToken(StateParser.VAR, 0)

        def ID(self):
            return self.getToken(StateParser.ID, 0)

        def COLON(self):
            return self.getToken(StateParser.COLON, 0)

        def type_(self):
            return self.getTypedRuleContext(StateParser.TypeContext,0)


        def LBRACKET(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.LBRACKET)
            else:
                return self.getToken(StateParser.LBRACKET, i)

        def NUMBER(self):
            return self.getToken(StateParser.NUMBER, 0)

        def RBRACKET(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.RBRACKET)
            else:
                return self.getToken(StateParser.RBRACKET, i)

        def EQUALS(self):
            return self.getToken(StateParser.EQUALS, 0)

        def id_list(self):
            return self.getTypedRuleContext(StateParser.Id_listContext,0)


        def getRuleIndex(self):
            return StateParser.RULE_array_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterArray_decl" ):
                listener.enterArray_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitArray_decl" ):
                listener.exitArray_decl(self)




    def array_decl(self):

        localctx = StateParser.Array_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_array_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 73
            self.match(StateParser.VAR)
            self.state = 74
            self.match(StateParser.ID)
            self.state = 75
            self.match(StateParser.COLON)
            self.state = 76
            self.type_()
            self.state = 77
            self.match(StateParser.LBRACKET)
            self.state = 78
            self.match(StateParser.NUMBER)
            self.state = 79
            self.match(StateParser.RBRACKET)
            self.state = 80
            self.match(StateParser.EQUALS)
            self.state = 81
            self.match(StateParser.LBRACKET)
            self.state = 82
            self.id_list()
            self.state = 83
            self.match(StateParser.RBRACKET)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Id_listContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def COMMA(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.COMMA)
            else:
                return self.getToken(StateParser.COMMA, i)

        def getRuleIndex(self):
            return StateParser.RULE_id_list

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterId_list" ):
                listener.enterId_list(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitId_list" ):
                listener.exitId_list(self)




    def id_list(self):

        localctx = StateParser.Id_listContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_id_list)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 86 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 85
                self.match(StateParser.ID)
                self.state = 88 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==16):
                    break

            self.state = 94
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2:
                self.state = 90
                self.match(StateParser.COMMA)
                self.state = 91
                self.match(StateParser.ID)
                self.state = 96
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class TypeContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def primitive_type(self):
            return self.getTypedRuleContext(StateParser.Primitive_typeContext,0)


        def ID(self):
            return self.getToken(StateParser.ID, 0)

        def getRuleIndex(self):
            return StateParser.RULE_type

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterType" ):
                listener.enterType(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitType" ):
                listener.exitType(self)




    def type_(self):

        localctx = StateParser.TypeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_type)
        try:
            self.state = 99
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [3, 4, 5, 8, 9]:
                self.enterOuterAlt(localctx, 1)
                self.state = 97
                self.primitive_type()
                pass
            elif token in [16]:
                self.enterOuterAlt(localctx, 2)
                self.state = 98
                self.match(StateParser.ID)
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


    class Primitive_typeContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def BIT(self):
            return self.getToken(StateParser.BIT, 0)

        def BOOL(self):
            return self.getToken(StateParser.BOOL, 0)

        def BYTE(self):
            return self.getToken(StateParser.BYTE, 0)

        def INT(self):
            return self.getToken(StateParser.INT, 0)

        def SHORT(self):
            return self.getToken(StateParser.SHORT, 0)

        def getRuleIndex(self):
            return StateParser.RULE_primitive_type

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterPrimitive_type" ):
                listener.enterPrimitive_type(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitPrimitive_type" ):
                listener.exitPrimitive_type(self)




    def primitive_type(self):

        localctx = StateParser.Primitive_typeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_primitive_type)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 101
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 824) != 0)):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





