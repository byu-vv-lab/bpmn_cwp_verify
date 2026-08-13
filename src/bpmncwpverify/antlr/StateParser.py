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
        4,1,18,121,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,1,0,5,0,24,8,0,10,0,12,0,27,
        9,0,1,0,5,0,30,8,0,10,0,12,0,33,9,0,1,0,5,0,36,8,0,10,0,12,0,39,
        9,0,1,0,5,0,42,8,0,10,0,12,0,45,9,0,1,0,4,0,48,8,0,11,0,12,0,49,
        1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,4,2,61,8,2,11,2,12,2,62,1,3,
        1,3,1,3,1,3,1,3,1,3,1,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,
        3,4,82,8,4,1,5,4,5,85,8,5,11,5,12,5,86,1,6,1,6,1,6,1,6,1,6,1,6,1,
        6,1,6,1,6,1,6,1,6,1,6,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,8,5,8,109,8,
        8,10,8,12,8,112,9,8,1,9,1,9,1,9,3,9,117,8,9,1,10,1,10,1,10,0,0,11,
        0,2,4,6,8,10,12,14,16,18,20,0,1,2,0,2,4,7,8,120,0,25,1,0,0,0,2,53,
        1,0,0,0,4,60,1,0,0,0,6,64,1,0,0,0,8,71,1,0,0,0,10,84,1,0,0,0,12,
        88,1,0,0,0,14,100,1,0,0,0,16,110,1,0,0,0,18,116,1,0,0,0,20,118,1,
        0,0,0,22,24,3,2,1,0,23,22,1,0,0,0,24,27,1,0,0,0,25,23,1,0,0,0,25,
        26,1,0,0,0,26,31,1,0,0,0,27,25,1,0,0,0,28,30,3,6,3,0,29,28,1,0,0,
        0,30,33,1,0,0,0,31,29,1,0,0,0,31,32,1,0,0,0,32,37,1,0,0,0,33,31,
        1,0,0,0,34,36,3,12,6,0,35,34,1,0,0,0,36,39,1,0,0,0,37,35,1,0,0,0,
        37,38,1,0,0,0,38,43,1,0,0,0,39,37,1,0,0,0,40,42,3,14,7,0,41,40,1,
        0,0,0,42,45,1,0,0,0,43,41,1,0,0,0,43,44,1,0,0,0,44,47,1,0,0,0,45,
        43,1,0,0,0,46,48,3,8,4,0,47,46,1,0,0,0,48,49,1,0,0,0,49,47,1,0,0,
        0,49,50,1,0,0,0,50,51,1,0,0,0,51,52,5,0,0,1,52,1,1,0,0,0,53,54,5,
        6,0,0,54,55,5,17,0,0,55,56,5,10,0,0,56,57,3,4,2,0,57,58,5,11,0,0,
        58,3,1,0,0,0,59,61,5,17,0,0,60,59,1,0,0,0,61,62,1,0,0,0,62,60,1,
        0,0,0,62,63,1,0,0,0,63,5,1,0,0,0,64,65,5,5,0,0,65,66,5,17,0,0,66,
        67,5,1,0,0,67,68,3,18,9,0,68,69,5,9,0,0,69,70,5,17,0,0,70,7,1,0,
        0,0,71,72,5,14,0,0,72,73,5,17,0,0,73,74,5,1,0,0,74,75,3,18,9,0,75,
        76,5,9,0,0,76,81,5,17,0,0,77,78,5,10,0,0,78,79,3,4,2,0,79,80,5,11,
        0,0,80,82,1,0,0,0,81,77,1,0,0,0,81,82,1,0,0,0,82,9,1,0,0,0,83,85,
        3,8,4,0,84,83,1,0,0,0,85,86,1,0,0,0,86,84,1,0,0,0,86,87,1,0,0,0,
        87,11,1,0,0,0,88,89,5,15,0,0,89,90,5,17,0,0,90,91,5,12,0,0,91,92,
        5,17,0,0,92,93,5,13,0,0,93,94,5,1,0,0,94,95,3,20,10,0,95,96,5,9,
        0,0,96,97,5,10,0,0,97,98,3,4,2,0,98,99,5,11,0,0,99,13,1,0,0,0,100,
        101,5,16,0,0,101,102,5,17,0,0,102,103,5,10,0,0,103,104,3,10,5,0,
        104,105,3,16,8,0,105,106,5,11,0,0,106,15,1,0,0,0,107,109,3,14,7,
        0,108,107,1,0,0,0,109,112,1,0,0,0,110,108,1,0,0,0,110,111,1,0,0,
        0,111,17,1,0,0,0,112,110,1,0,0,0,113,117,3,20,10,0,114,117,5,16,
        0,0,115,117,5,17,0,0,116,113,1,0,0,0,116,114,1,0,0,0,116,115,1,0,
        0,0,117,19,1,0,0,0,118,119,7,0,0,0,119,21,1,0,0,0,10,25,31,37,43,
        49,62,81,86,110,116
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
    RULE_typedef_decl = 7
    RULE_typedef_decl_set = 8
    RULE_type = 9
    RULE_primitive_type = 10

    ruleNames =  [ "state", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl", "var_set", "array_decl", "typedef_decl", 
                   "typedef_decl_set", "type", "primitive_type" ]

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
            self.state = 25
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==6:
                self.state = 22
                self.enum_type_decl()
                self.state = 27
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 31
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 28
                self.const_var_decl()
                self.state = 33
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 37
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 34
                self.array_decl()
                self.state = 39
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 43
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==16:
                self.state = 40
                self.typedef_decl()
                self.state = 45
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 47 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 46
                self.var_decl()
                self.state = 49 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==14):
                    break

            self.state = 51
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
            self.state = 53
            self.match(StateParser.ENUM)
            self.state = 54
            self.match(StateParser.ID)
            self.state = 55
            self.match(StateParser.LCURLY)
            self.state = 56
            self.id_set()
            self.state = 57
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
            self.state = 60 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 59
                self.match(StateParser.ID)
                self.state = 62 
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
            self.state = 64
            self.match(StateParser.CONST)
            self.state = 65
            self.match(StateParser.ID)
            self.state = 66
            self.match(StateParser.COLON)
            self.state = 67
            self.type_()
            self.state = 68
            self.match(StateParser.EQUALS)
            self.state = 69
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
            self.state = 71
            self.match(StateParser.VAR)
            self.state = 72
            self.match(StateParser.ID)
            self.state = 73
            self.match(StateParser.COLON)
            self.state = 74
            self.type_()
            self.state = 75
            self.match(StateParser.EQUALS)
            self.state = 76
            self.match(StateParser.ID)
            self.state = 81
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==10:
                self.state = 77
                self.match(StateParser.LCURLY)
                self.state = 78
                self.id_set()
                self.state = 79
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
            self.state = 84 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 83
                self.var_decl()
                self.state = 86 
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
            self.state = 88
            self.match(StateParser.ARRAY)
            self.state = 89
            self.match(StateParser.ID)
            self.state = 90
            self.match(StateParser.LBRACKET)
            self.state = 91
            self.match(StateParser.ID)
            self.state = 92
            self.match(StateParser.RBRACKET)
            self.state = 93
            self.match(StateParser.COLON)
            self.state = 94
            self.primitive_type()
            self.state = 95
            self.match(StateParser.EQUALS)
            self.state = 96
            self.match(StateParser.LCURLY)
            self.state = 97
            self.id_set()
            self.state = 98
            self.match(StateParser.RCURLY)
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
        self.enterRule(localctx, 14, self.RULE_typedef_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 100
            self.match(StateParser.TYPEDEF)
            self.state = 101
            self.match(StateParser.ID)
            self.state = 102
            self.match(StateParser.LCURLY)
            self.state = 103
            self.var_set()
            self.state = 104
            self.typedef_decl_set()
            self.state = 105
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
        self.enterRule(localctx, 16, self.RULE_typedef_decl_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 110
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==16:
                self.state = 107
                self.typedef_decl()
                self.state = 112
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
        self.enterRule(localctx, 18, self.RULE_type)
        try:
            self.state = 116
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [2, 3, 4, 7, 8]:
                self.enterOuterAlt(localctx, 1)
                self.state = 113
                self.primitive_type()
                pass
            elif token in [16]:
                self.enterOuterAlt(localctx, 2)
                self.state = 114
                self.match(StateParser.TYPEDEF)
                pass
            elif token in [17]:
                self.enterOuterAlt(localctx, 3)
                self.state = 115
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
        self.enterRule(localctx, 20, self.RULE_primitive_type)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 118
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





