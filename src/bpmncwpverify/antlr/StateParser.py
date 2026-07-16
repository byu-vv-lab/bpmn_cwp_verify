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
<<<<<<< HEAD
        4,1,17,90,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,1,0,5,0,18,8,0,10,0,12,0,21,9,0,1,0,5,0,24,8,0,10,0,12,
        0,27,9,0,1,0,5,0,30,8,0,10,0,12,0,33,9,0,1,0,4,0,36,8,0,11,0,12,
        0,37,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,4,2,49,8,2,11,2,12,2,50,
        1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,1,4,
        1,4,3,4,70,8,4,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,
        6,1,6,3,6,86,8,6,1,7,1,7,1,7,0,0,8,0,2,4,6,8,10,12,14,0,1,2,0,2,
        4,7,8,88,0,19,1,0,0,0,2,41,1,0,0,0,4,48,1,0,0,0,6,52,1,0,0,0,8,59,
        1,0,0,0,10,71,1,0,0,0,12,85,1,0,0,0,14,87,1,0,0,0,16,18,3,2,1,0,
        17,16,1,0,0,0,18,21,1,0,0,0,19,17,1,0,0,0,19,20,1,0,0,0,20,25,1,
        0,0,0,21,19,1,0,0,0,22,24,3,6,3,0,23,22,1,0,0,0,24,27,1,0,0,0,25,
        23,1,0,0,0,25,26,1,0,0,0,26,31,1,0,0,0,27,25,1,0,0,0,28,30,3,10,
        5,0,29,28,1,0,0,0,30,33,1,0,0,0,31,29,1,0,0,0,31,32,1,0,0,0,32,35,
        1,0,0,0,33,31,1,0,0,0,34,36,3,8,4,0,35,34,1,0,0,0,36,37,1,0,0,0,
        37,35,1,0,0,0,37,38,1,0,0,0,38,39,1,0,0,0,39,40,5,0,0,1,40,1,1,0,
        0,0,41,42,5,6,0,0,42,43,5,16,0,0,43,44,5,10,0,0,44,45,3,4,2,0,45,
        46,5,11,0,0,46,3,1,0,0,0,47,49,5,16,0,0,48,47,1,0,0,0,49,50,1,0,
        0,0,50,48,1,0,0,0,50,51,1,0,0,0,51,5,1,0,0,0,52,53,5,5,0,0,53,54,
        5,16,0,0,54,55,5,1,0,0,55,56,3,12,6,0,56,57,5,9,0,0,57,58,5,16,0,
        0,58,7,1,0,0,0,59,60,5,14,0,0,60,61,5,16,0,0,61,62,5,1,0,0,62,63,
        3,12,6,0,63,64,5,9,0,0,64,69,5,16,0,0,65,66,5,10,0,0,66,67,3,4,2,
        0,67,68,5,11,0,0,68,70,1,0,0,0,69,65,1,0,0,0,69,70,1,0,0,0,70,9,
        1,0,0,0,71,72,5,15,0,0,72,73,5,16,0,0,73,74,5,12,0,0,74,75,5,16,
        0,0,75,76,5,13,0,0,76,77,5,1,0,0,77,78,3,14,7,0,78,79,5,9,0,0,79,
        80,5,10,0,0,80,81,3,4,2,0,81,82,5,11,0,0,82,11,1,0,0,0,83,86,3,14,
        7,0,84,86,5,16,0,0,85,83,1,0,0,0,85,84,1,0,0,0,86,13,1,0,0,0,87,
        88,7,0,0,0,88,15,1,0,0,0,7,19,25,31,37,50,69,85
=======
        4,1,15,101,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,1,0,5,0,22,8,0,10,0,12,0,25,9,0,1,0,5,
        0,28,8,0,10,0,12,0,31,9,0,1,0,5,0,34,8,0,10,0,12,0,37,9,0,1,0,4,
        0,40,8,0,11,0,12,0,41,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,4,2,53,
        8,2,11,2,12,2,54,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,4,1,4,1,4,1,4,1,4,
        1,4,1,4,1,4,1,4,1,4,3,4,74,8,4,1,5,4,5,77,8,5,11,5,12,5,78,1,6,1,
        6,1,6,1,6,1,6,1,6,1,6,1,7,5,7,89,8,7,10,7,12,7,92,9,7,1,8,1,8,1,
        8,3,8,97,8,8,1,9,1,9,1,9,0,0,10,0,2,4,6,8,10,12,14,16,18,0,1,2,0,
        2,4,7,8,100,0,23,1,0,0,0,2,45,1,0,0,0,4,52,1,0,0,0,6,56,1,0,0,0,
        8,63,1,0,0,0,10,76,1,0,0,0,12,80,1,0,0,0,14,90,1,0,0,0,16,96,1,0,
        0,0,18,98,1,0,0,0,20,22,3,2,1,0,21,20,1,0,0,0,22,25,1,0,0,0,23,21,
        1,0,0,0,23,24,1,0,0,0,24,29,1,0,0,0,25,23,1,0,0,0,26,28,3,6,3,0,
        27,26,1,0,0,0,28,31,1,0,0,0,29,27,1,0,0,0,29,30,1,0,0,0,30,35,1,
        0,0,0,31,29,1,0,0,0,32,34,3,12,6,0,33,32,1,0,0,0,34,37,1,0,0,0,35,
        33,1,0,0,0,35,36,1,0,0,0,36,39,1,0,0,0,37,35,1,0,0,0,38,40,3,8,4,
        0,39,38,1,0,0,0,40,41,1,0,0,0,41,39,1,0,0,0,41,42,1,0,0,0,42,43,
        1,0,0,0,43,44,5,0,0,1,44,1,1,0,0,0,45,46,5,6,0,0,46,47,5,14,0,0,
        47,48,5,10,0,0,48,49,3,4,2,0,49,50,5,11,0,0,50,3,1,0,0,0,51,53,5,
        14,0,0,52,51,1,0,0,0,53,54,1,0,0,0,54,52,1,0,0,0,54,55,1,0,0,0,55,
        5,1,0,0,0,56,57,5,5,0,0,57,58,5,14,0,0,58,59,5,1,0,0,59,60,3,16,
        8,0,60,61,5,9,0,0,61,62,5,14,0,0,62,7,1,0,0,0,63,64,5,12,0,0,64,
        65,5,14,0,0,65,66,5,1,0,0,66,67,3,16,8,0,67,68,5,9,0,0,68,73,5,14,
        0,0,69,70,5,10,0,0,70,71,3,4,2,0,71,72,5,11,0,0,72,74,1,0,0,0,73,
        69,1,0,0,0,73,74,1,0,0,0,74,9,1,0,0,0,75,77,3,8,4,0,76,75,1,0,0,
        0,77,78,1,0,0,0,78,76,1,0,0,0,78,79,1,0,0,0,79,11,1,0,0,0,80,81,
        5,13,0,0,81,82,5,14,0,0,82,83,5,10,0,0,83,84,3,10,5,0,84,85,3,14,
        7,0,85,86,5,11,0,0,86,13,1,0,0,0,87,89,3,12,6,0,88,87,1,0,0,0,89,
        92,1,0,0,0,90,88,1,0,0,0,90,91,1,0,0,0,91,15,1,0,0,0,92,90,1,0,0,
        0,93,97,3,18,9,0,94,97,5,13,0,0,95,97,5,14,0,0,96,93,1,0,0,0,96,
        94,1,0,0,0,96,95,1,0,0,0,97,17,1,0,0,0,98,99,7,0,0,0,99,19,1,0,0,
        0,9,23,29,35,41,54,73,78,90,96
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
    ]

class StateParser ( Parser ):

    grammarFileName = "State.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'bit'", "'bool'", "'byte'", "'const'", 
                     "'enum'", "'int'", "'short'", "'='", "'{'", "'}'", 
<<<<<<< HEAD
                     "'['", "']'", "'var'", "'array'" ]

    symbolicNames = [ "<INVALID>", "COLON", "BIT", "BOOL", "BYTE", "CONST", 
                      "ENUM", "INT", "SHORT", "EQUALS", "LCURLY", "RCURLY", 
                      "LBRACKET", "RBRACKET", "VAR", "ARRAY", "ID", "WS" ]
=======
                     "'var'", "'typedef'" ]

    symbolicNames = [ "<INVALID>", "COLON", "BIT", "BOOL", "BYTE", "CONST", 
                      "ENUM", "INT", "SHORT", "EQUALS", "LCURLY", "RCURLY", 
                      "VAR", "TYPEDEF", "ID", "WS" ]
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)

    RULE_state = 0
    RULE_enum_type_decl = 1
    RULE_id_set = 2
    RULE_const_var_decl = 3
    RULE_var_decl = 4
<<<<<<< HEAD
    RULE_array_decl = 5
    RULE_type = 6
    RULE_primitive_type = 7

    ruleNames =  [ "state", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl", "array_decl", "type", "primitive_type" ]
=======
    RULE_var_set = 5
    RULE_typedef_decl = 6
    RULE_typedef_decl_set = 7
    RULE_type = 8
    RULE_primitive_type = 9

    ruleNames =  [ "state", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl", "var_set", "typedef_decl", "typedef_decl_set", 
                   "type", "primitive_type" ]
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)

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
<<<<<<< HEAD
    LBRACKET=12
    RBRACKET=13
    VAR=14
    ARRAY=15
    ID=16
    WS=17
=======
    VAR=12
    TYPEDEF=13
    ID=14
    WS=15
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)

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


<<<<<<< HEAD
        def array_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Array_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Array_declContext,i)
=======
        def typedef_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Typedef_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Typedef_declContext,i)
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)


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
<<<<<<< HEAD
            self.state = 19
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==6:
                self.state = 16
                self.enum_type_decl()
                self.state = 21
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 25
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 22
                self.const_var_decl()
                self.state = 27
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 31
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==15:
                self.state = 28
                self.array_decl()
                self.state = 33
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 35 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 34
                self.var_decl()
                self.state = 37 
=======
            self.state = 23
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==6:
                self.state = 20
                self.enum_type_decl()
                self.state = 25
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 29
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==5:
                self.state = 26
                self.const_var_decl()
                self.state = 31
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 35
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==13:
                self.state = 32
                self.typedef_decl()
                self.state = 37
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 39 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 38
                self.var_decl()
                self.state = 41 
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==14):
                    break

<<<<<<< HEAD
            self.state = 39
=======
            self.state = 43
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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
<<<<<<< HEAD
            self.state = 41
            self.match(StateParser.ENUM)
            self.state = 42
            self.match(StateParser.ID)
            self.state = 43
            self.match(StateParser.LCURLY)
            self.state = 44
            self.id_set()
            self.state = 45
=======
            self.state = 45
            self.match(StateParser.ENUM)
            self.state = 46
            self.match(StateParser.ID)
            self.state = 47
            self.match(StateParser.LCURLY)
            self.state = 48
            self.id_set()
            self.state = 49
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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
<<<<<<< HEAD
            self.state = 48 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 47
                self.match(StateParser.ID)
                self.state = 50 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==16):
=======
            self.state = 52 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 51
                self.match(StateParser.ID)
                self.state = 54 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==14):
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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
<<<<<<< HEAD
            self.state = 52
            self.match(StateParser.CONST)
            self.state = 53
            self.match(StateParser.ID)
            self.state = 54
            self.match(StateParser.COLON)
            self.state = 55
            self.type_()
            self.state = 56
            self.match(StateParser.EQUALS)
            self.state = 57
=======
            self.state = 56
            self.match(StateParser.CONST)
            self.state = 57
            self.match(StateParser.ID)
            self.state = 58
            self.match(StateParser.COLON)
            self.state = 59
            self.type_()
            self.state = 60
            self.match(StateParser.EQUALS)
            self.state = 61
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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
<<<<<<< HEAD
            self.state = 59
            self.match(StateParser.VAR)
            self.state = 60
            self.match(StateParser.ID)
            self.state = 61
            self.match(StateParser.COLON)
            self.state = 62
            self.type_()
            self.state = 63
            self.match(StateParser.EQUALS)
            self.state = 64
            self.match(StateParser.ID)
            self.state = 69
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==10:
                self.state = 65
                self.match(StateParser.LCURLY)
                self.state = 66
                self.id_set()
                self.state = 67
=======
            self.state = 63
            self.match(StateParser.VAR)
            self.state = 64
            self.match(StateParser.ID)
            self.state = 65
            self.match(StateParser.COLON)
            self.state = 66
            self.type_()
            self.state = 67
            self.match(StateParser.EQUALS)
            self.state = 68
            self.match(StateParser.ID)
            self.state = 73
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==10:
                self.state = 69
                self.match(StateParser.LCURLY)
                self.state = 70
                self.id_set()
                self.state = 71
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
                self.match(StateParser.RCURLY)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


<<<<<<< HEAD
    class Array_declContext(ParserRuleContext):
=======
    class Var_setContext(ParserRuleContext):
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

<<<<<<< HEAD
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
=======
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
            self.state = 76 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 75
                self.var_decl()
                self.state = 78 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==12):
                    break

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
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

<<<<<<< HEAD
        def id_set(self):
            return self.getTypedRuleContext(StateParser.Id_setContext,0)
=======
        def var_set(self):
            return self.getTypedRuleContext(StateParser.Var_setContext,0)


        def typedef_decl_set(self):
            return self.getTypedRuleContext(StateParser.Typedef_decl_setContext,0)
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)


        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

        def getRuleIndex(self):
<<<<<<< HEAD
            return StateParser.RULE_array_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterArray_decl" ):
                listener.enterArray_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitArray_decl" ):
                listener.exitArray_decl(self)
=======
            return StateParser.RULE_typedef_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterTypedef_decl" ):
                listener.enterTypedef_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitTypedef_decl" ):
                listener.exitTypedef_decl(self)
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)




<<<<<<< HEAD
    def array_decl(self):

        localctx = StateParser.Array_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_array_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 71
            self.match(StateParser.ARRAY)
            self.state = 72
            self.match(StateParser.ID)
            self.state = 73
            self.match(StateParser.LBRACKET)
            self.state = 74
            self.match(StateParser.ID)
            self.state = 75
            self.match(StateParser.RBRACKET)
            self.state = 76
            self.match(StateParser.COLON)
            self.state = 77
            self.primitive_type()
            self.state = 78
            self.match(StateParser.EQUALS)
            self.state = 79
            self.match(StateParser.LCURLY)
            self.state = 80
            self.id_set()
            self.state = 81
=======
    def typedef_decl(self):

        localctx = StateParser.Typedef_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_typedef_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 80
            self.match(StateParser.TYPEDEF)
            self.state = 81
            self.match(StateParser.ID)
            self.state = 82
            self.match(StateParser.LCURLY)
            self.state = 83
            self.var_set()
            self.state = 84
            self.typedef_decl_set()
            self.state = 85
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
            self.match(StateParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


<<<<<<< HEAD
=======
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
        self.enterRule(localctx, 14, self.RULE_typedef_decl_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 90
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==13:
                self.state = 87
                self.typedef_decl()
                self.state = 92
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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
<<<<<<< HEAD
        self.enterRule(localctx, 12, self.RULE_type)
        try:
            self.state = 85
=======
        self.enterRule(localctx, 16, self.RULE_type)
        try:
            self.state = 96
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [2, 3, 4, 7, 8]:
                self.enterOuterAlt(localctx, 1)
<<<<<<< HEAD
                self.state = 83
=======
                self.state = 93
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
                self.primitive_type()
                pass
            elif token in [16]:
                self.enterOuterAlt(localctx, 2)
<<<<<<< HEAD
                self.state = 84
=======
                self.state = 94
                self.match(StateParser.TYPEDEF)
                pass
            elif token in [14]:
                self.enterOuterAlt(localctx, 3)
                self.state = 95
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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
<<<<<<< HEAD
        self.enterRule(localctx, 14, self.RULE_primitive_type)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 87
=======
        self.enterRule(localctx, 18, self.RULE_primitive_type)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 98
>>>>>>> 28ed538 (Added typedefs to the state.g4 and rebuilt antlr files)
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





