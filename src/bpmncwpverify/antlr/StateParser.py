# Generated from antlr/State.g4 by ANTLR 4.13.2
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
        4,1,18,130,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,1,0,5,0,26,8,0,10,
        0,12,0,29,9,0,1,0,5,0,32,8,0,10,0,12,0,35,9,0,1,0,5,0,38,8,0,10,
        0,12,0,41,9,0,1,0,5,0,44,8,0,10,0,12,0,47,9,0,1,0,4,0,50,8,0,11,
        0,12,0,51,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,4,2,63,8,2,11,2,12,
        2,64,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,
        1,4,1,4,3,4,84,8,4,1,5,4,5,87,8,5,11,5,12,5,88,1,6,1,6,1,6,1,6,1,
        6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,7,5,7,104,8,7,10,7,12,7,107,9,7,
        1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,8,1,9,5,9,118,8,9,10,9,12,9,121,9,
        9,1,10,1,10,1,10,3,10,126,8,10,1,11,1,11,1,11,0,0,12,0,2,4,6,8,10,
        12,14,16,18,20,22,0,1,2,0,2,4,7,8,129,0,27,1,0,0,0,2,55,1,0,0,0,
        4,62,1,0,0,0,6,66,1,0,0,0,8,73,1,0,0,0,10,86,1,0,0,0,12,90,1,0,0,
        0,14,105,1,0,0,0,16,108,1,0,0,0,18,119,1,0,0,0,20,125,1,0,0,0,22,
        127,1,0,0,0,24,26,3,2,1,0,25,24,1,0,0,0,26,29,1,0,0,0,27,25,1,0,
        0,0,27,28,1,0,0,0,28,33,1,0,0,0,29,27,1,0,0,0,30,32,3,6,3,0,31,30,
        1,0,0,0,32,35,1,0,0,0,33,31,1,0,0,0,33,34,1,0,0,0,34,39,1,0,0,0,
        35,33,1,0,0,0,36,38,3,12,6,0,37,36,1,0,0,0,38,41,1,0,0,0,39,37,1,
        0,0,0,39,40,1,0,0,0,40,45,1,0,0,0,41,39,1,0,0,0,42,44,3,16,8,0,43,
        42,1,0,0,0,44,47,1,0,0,0,45,43,1,0,0,0,45,46,1,0,0,0,46,49,1,0,0,
        0,47,45,1,0,0,0,48,50,3,8,4,0,49,48,1,0,0,0,50,51,1,0,0,0,51,49,
        1,0,0,0,51,52,1,0,0,0,52,53,1,0,0,0,53,54,5,0,0,1,54,1,1,0,0,0,55,
        56,5,6,0,0,56,57,5,17,0,0,57,58,5,10,0,0,58,59,3,4,2,0,59,60,5,11,
        0,0,60,3,1,0,0,0,61,63,5,17,0,0,62,61,1,0,0,0,63,64,1,0,0,0,64,62,
        1,0,0,0,64,65,1,0,0,0,65,5,1,0,0,0,66,67,5,5,0,0,67,68,5,17,0,0,
        68,69,5,1,0,0,69,70,3,20,10,0,70,71,5,9,0,0,71,72,5,17,0,0,72,7,
        1,0,0,0,73,74,5,14,0,0,74,75,5,17,0,0,75,76,5,1,0,0,76,77,3,20,10,
        0,77,78,5,9,0,0,78,83,5,17,0,0,79,80,5,10,0,0,80,81,3,4,2,0,81,82,
        5,11,0,0,82,84,1,0,0,0,83,79,1,0,0,0,83,84,1,0,0,0,84,9,1,0,0,0,
        85,87,3,8,4,0,86,85,1,0,0,0,87,88,1,0,0,0,88,86,1,0,0,0,88,89,1,
        0,0,0,89,11,1,0,0,0,90,91,5,15,0,0,91,92,5,17,0,0,92,93,5,12,0,0,
        93,94,5,17,0,0,94,95,5,13,0,0,95,96,5,1,0,0,96,97,3,22,11,0,97,98,
        5,9,0,0,98,99,5,10,0,0,99,100,3,4,2,0,100,101,5,11,0,0,101,13,1,
        0,0,0,102,104,3,12,6,0,103,102,1,0,0,0,104,107,1,0,0,0,105,103,1,
        0,0,0,105,106,1,0,0,0,106,15,1,0,0,0,107,105,1,0,0,0,108,109,5,16,
        0,0,109,110,5,17,0,0,110,111,5,10,0,0,111,112,3,14,7,0,112,113,3,
        10,5,0,113,114,3,18,9,0,114,115,5,11,0,0,115,17,1,0,0,0,116,118,
        3,16,8,0,117,116,1,0,0,0,118,121,1,0,0,0,119,117,1,0,0,0,119,120,
        1,0,0,0,120,19,1,0,0,0,121,119,1,0,0,0,122,126,3,22,11,0,123,126,
        5,16,0,0,124,126,5,17,0,0,125,122,1,0,0,0,125,123,1,0,0,0,125,124,
        1,0,0,0,126,21,1,0,0,0,127,128,7,0,0,0,128,23,1,0,0,0,11,27,33,39,
        45,51,64,83,88,105,119,125
    ]

class StateParser ( Parser ):

    grammarFileName = "State.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'bit'", "'bool'", "'byte'", "'const'", 
                     "'enum'", "'int'", "'short'", "'='", "'{'", "'}'", 
                     "'['", "']'", "'var'", "'array'", "'typedef'" ]

    symbolicNames = [ "<INVALID>", "COLON", "BIT", "BOOL", "BYTE", "CONST", 
                      "ENUM", "INT", "SHORT", "EQUALS", "LCURLY", "RCURLY", 
                      "LBRACKET", "RBRACKET", "VAR", "ARRAY", "TYPEDEF", 
                      "ID", "WS" ]

    RULE_state = 0
    RULE_enum_type_decl = 1
    RULE_id_set = 2
    RULE_const_var_decl = 3
    RULE_var_decl = 4
    RULE_var_set = 5
    RULE_array_decl = 6
    RULE_array_decl_set = 7
    RULE_typedef_decl = 8
    RULE_typedef_decl_set = 9
    RULE_type = 10
    RULE_primitive_type = 11

    ruleNames =  [ "state", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl", "var_set", "array_decl", "array_decl_set", 
                   "typedef_decl", "typedef_decl_set", "type", "primitive_type" ]

    EOF = Token.EOF
    COLON=1
    BIT=2
    BOOL=3
    BYTE=4
    CONST=5
    ENUM=6
    INT=7
    SHORT=8
    EQUALS=9
    LCURLY=10
    RCURLY=11
    LBRACKET=12
    RBRACKET=13
    VAR=14
    ARRAY=15
    TYPEDEF=16
    ID=17
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


        def typedef_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Typedef_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Typedef_declContext,i)


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




    def state(self):

        localctx = StateParser.StateContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_state)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 27
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==6:
                self.state = 24
                self.enum_type_decl()
                self.state = 29
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 33
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 30
                self.const_var_decl()
                self.state = 35
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 39
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 36
                self.array_decl()
                self.state = 41
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 45
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==16:
                self.state = 42
                self.typedef_decl()
                self.state = 47
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 49 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 48
                self.var_decl()
                self.state = 51 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==14):
                    break

            self.state = 53
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
            self.state = 55
            self.match(StateParser.ENUM)
            self.state = 56
            self.match(StateParser.ID)
            self.state = 57
            self.match(StateParser.LCURLY)
            self.state = 58
            self.id_set()
            self.state = 59
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
            self.state = 62 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 61
                self.match(StateParser.ID)
                self.state = 64 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==17):
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
            self.state = 66
            self.match(StateParser.CONST)
            self.state = 67
            self.match(StateParser.ID)
            self.state = 68
            self.match(StateParser.COLON)
            self.state = 69
            self.type_()
            self.state = 70
            self.match(StateParser.EQUALS)
            self.state = 71
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
            self.state = 73
            self.match(StateParser.VAR)
            self.state = 74
            self.match(StateParser.ID)
            self.state = 75
            self.match(StateParser.COLON)
            self.state = 76
            self.type_()
            self.state = 77
            self.match(StateParser.EQUALS)
            self.state = 78
            self.match(StateParser.ID)
            self.state = 83
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==10:
                self.state = 79
                self.match(StateParser.LCURLY)
                self.state = 80
                self.id_set()
                self.state = 81
                self.match(StateParser.RCURLY)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Var_setContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def var_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Var_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Var_declContext,i)


        def getRuleIndex(self):
            return StateParser.RULE_var_set

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterVar_set" ):
                listener.enterVar_set(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitVar_set" ):
                listener.exitVar_set(self)




    def var_set(self):

        localctx = StateParser.Var_setContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_var_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 86 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 85
                self.var_decl()
                self.state = 88 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==14):
                    break

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

        def ARRAY(self):
            return self.getToken(StateParser.ARRAY, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def LBRACKET(self):
            return self.getToken(StateParser.LBRACKET, 0)

        def RBRACKET(self):
            return self.getToken(StateParser.RBRACKET, 0)

        def COLON(self):
            return self.getToken(StateParser.COLON, 0)

        def primitive_type(self):
            return self.getTypedRuleContext(StateParser.Primitive_typeContext,0)


        def EQUALS(self):
            return self.getToken(StateParser.EQUALS, 0)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def id_set(self):
            return self.getTypedRuleContext(StateParser.Id_setContext,0)


        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

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
        self.enterRule(localctx, 12, self.RULE_array_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 90
            self.match(StateParser.ARRAY)
            self.state = 91
            self.match(StateParser.ID)
            self.state = 92
            self.match(StateParser.LBRACKET)
            self.state = 93
            self.match(StateParser.ID)
            self.state = 94
            self.match(StateParser.RBRACKET)
            self.state = 95
            self.match(StateParser.COLON)
            self.state = 96
            self.primitive_type()
            self.state = 97
            self.match(StateParser.EQUALS)
            self.state = 98
            self.match(StateParser.LCURLY)
            self.state = 99
            self.id_set()
            self.state = 100
            self.match(StateParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Array_decl_setContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def array_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Array_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Array_declContext,i)


        def getRuleIndex(self):
            return StateParser.RULE_array_decl_set

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterArray_decl_set" ):
                listener.enterArray_decl_set(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitArray_decl_set" ):
                listener.exitArray_decl_set(self)




    def array_decl_set(self):

        localctx = StateParser.Array_decl_setContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_array_decl_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 105
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 102
                self.array_decl()
                self.state = 107
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Typedef_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def TYPEDEF(self):
            return self.getToken(StateParser.TYPEDEF, 0)

        def ID(self):
            return self.getToken(StateParser.ID, 0)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def array_decl_set(self):
            return self.getTypedRuleContext(StateParser.Array_decl_setContext,0)


        def var_set(self):
            return self.getTypedRuleContext(StateParser.Var_setContext,0)


        def typedef_decl_set(self):
            return self.getTypedRuleContext(StateParser.Typedef_decl_setContext,0)


        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateParser.RULE_typedef_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterTypedef_decl" ):
                listener.enterTypedef_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitTypedef_decl" ):
                listener.exitTypedef_decl(self)




    def typedef_decl(self):

        localctx = StateParser.Typedef_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_typedef_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 108
            self.match(StateParser.TYPEDEF)
            self.state = 109
            self.match(StateParser.ID)
            self.state = 110
            self.match(StateParser.LCURLY)
            self.state = 111
            self.array_decl_set()
            self.state = 112
            self.var_set()
            self.state = 113
            self.typedef_decl_set()
            self.state = 114
            self.match(StateParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Typedef_decl_setContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def typedef_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Typedef_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Typedef_declContext,i)


        def getRuleIndex(self):
            return StateParser.RULE_typedef_decl_set

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterTypedef_decl_set" ):
                listener.enterTypedef_decl_set(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitTypedef_decl_set" ):
                listener.exitTypedef_decl_set(self)




    def typedef_decl_set(self):

        localctx = StateParser.Typedef_decl_setContext(self, self._ctx, self.state)
        self.enterRule(localctx, 18, self.RULE_typedef_decl_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 119
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==16:
                self.state = 116
                self.typedef_decl()
                self.state = 121
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


        def TYPEDEF(self):
            return self.getToken(StateParser.TYPEDEF, 0)

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
        self.enterRule(localctx, 20, self.RULE_type)
        try:
            self.state = 125
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [2, 3, 4, 7, 8]:
                self.enterOuterAlt(localctx, 1)
                self.state = 122
                self.primitive_type()
                pass
            elif token in [16]:
                self.enterOuterAlt(localctx, 2)
                self.state = 123
                self.match(StateParser.TYPEDEF)
                pass
            elif token in [17]:
                self.enterOuterAlt(localctx, 3)
                self.state = 124
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
        self.enterRule(localctx, 22, self.RULE_primitive_type)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 127
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 412) != 0)):
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





