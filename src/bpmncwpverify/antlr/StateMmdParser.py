# Generated from antlr/StateMmd.g4 by ANTLR 4.13.2
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
        4,1,23,108,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,6,7,
        6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,1,0,1,0,5,0,27,8,0,
        10,0,12,0,30,9,0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,3,1,40,8,1,1,2,
        1,2,1,2,1,2,1,2,1,2,1,3,1,3,4,3,50,8,3,11,3,12,3,51,1,4,1,4,1,4,
        1,4,1,4,1,4,1,4,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,1,5,3,5,70,8,5,1,
        5,1,5,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,7,1,7,3,7,86,8,7,
        1,8,1,8,1,9,1,9,1,9,1,9,1,10,1,10,1,10,1,10,1,10,5,10,99,8,10,10,
        10,12,10,102,9,10,1,10,1,10,1,11,1,11,1,11,0,0,12,0,2,4,6,8,10,12,
        14,16,18,20,22,0,2,1,0,7,11,1,0,17,21,106,0,24,1,0,0,0,2,39,1,0,
        0,0,4,41,1,0,0,0,6,49,1,0,0,0,8,53,1,0,0,0,10,60,1,0,0,0,12,73,1,
        0,0,0,14,85,1,0,0,0,16,87,1,0,0,0,18,89,1,0,0,0,20,93,1,0,0,0,22,
        105,1,0,0,0,24,28,5,1,0,0,25,27,3,2,1,0,26,25,1,0,0,0,27,30,1,0,
        0,0,28,26,1,0,0,0,28,29,1,0,0,0,29,31,1,0,0,0,30,28,1,0,0,0,31,32,
        5,0,0,1,32,1,1,0,0,0,33,40,3,4,2,0,34,40,3,8,4,0,35,40,3,12,6,0,
        36,40,3,10,5,0,37,40,3,18,9,0,38,40,3,20,10,0,39,33,1,0,0,0,39,34,
        1,0,0,0,39,35,1,0,0,0,39,36,1,0,0,0,39,37,1,0,0,0,39,38,1,0,0,0,
        40,3,1,0,0,0,41,42,5,2,0,0,42,43,5,21,0,0,43,44,5,13,0,0,44,45,3,
        6,3,0,45,46,5,14,0,0,46,5,1,0,0,0,47,50,5,21,0,0,48,50,3,16,8,0,
        49,47,1,0,0,0,49,48,1,0,0,0,50,51,1,0,0,0,51,49,1,0,0,0,51,52,1,
        0,0,0,52,7,1,0,0,0,53,54,5,2,0,0,54,55,5,21,0,0,55,56,5,13,0,0,56,
        57,5,3,0,0,57,58,3,14,7,0,58,59,5,14,0,0,59,9,1,0,0,0,60,61,5,2,
        0,0,61,62,5,21,0,0,62,63,5,13,0,0,63,64,5,4,0,0,64,69,3,14,7,0,65,
        66,5,13,0,0,66,67,3,6,3,0,67,68,5,14,0,0,68,70,1,0,0,0,69,65,1,0,
        0,0,69,70,1,0,0,0,70,71,1,0,0,0,71,72,5,14,0,0,72,11,1,0,0,0,73,
        74,5,2,0,0,74,75,5,21,0,0,75,76,5,13,0,0,76,77,5,5,0,0,77,78,3,16,
        8,0,78,79,5,15,0,0,79,80,5,21,0,0,80,81,5,16,0,0,81,82,5,14,0,0,
        82,13,1,0,0,0,83,86,3,16,8,0,84,86,5,21,0,0,85,83,1,0,0,0,85,84,
        1,0,0,0,86,15,1,0,0,0,87,88,7,0,0,0,88,17,1,0,0,0,89,90,5,21,0,0,
        90,91,5,12,0,0,91,92,3,14,7,0,92,19,1,0,0,0,93,94,5,2,0,0,94,95,
        5,21,0,0,95,96,5,13,0,0,96,100,5,6,0,0,97,99,3,22,11,0,98,97,1,0,
        0,0,99,102,1,0,0,0,100,98,1,0,0,0,100,101,1,0,0,0,101,103,1,0,0,
        0,102,100,1,0,0,0,103,104,5,14,0,0,104,21,1,0,0,0,105,106,7,1,0,
        0,106,23,1,0,0,0,7,28,39,49,51,69,85,100
    ]

class StateMmdParser ( Parser ):

    grammarFileName = "StateMmd.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'classDiagram'", "'class'", "'<<constant>>'", 
                     "'<<variable>>'", "'<<array>>'", "<INVALID>", "'bit'", 
                     "'bool'", "'byte'", "'int'", "'short'", "'-->'", "'{'", 
                     "'}'", "'['", "']'", "'.'", "'/'", "'-'", "','" ]

    symbolicNames = [ "<INVALID>", "CLASS_DIAGRAM", "CLASS", "CONSTANT", 
                      "VARIABLE", "ARRAY", "NOTE", "BIT", "BOOL", "BYTE", 
                      "INT", "SHORT", "ARROW", "LCURLY", "RCURLY", "LBRACKET", 
                      "RBRACKET", "DOT", "SLASH", "DASH", "COMMA", "ID", 
                      "COMMENT", "WS" ]

    RULE_stateFile = 0
    RULE_element = 1
    RULE_enum_type_decl = 2
    RULE_id_set = 3
    RULE_const_var_decl = 4
    RULE_var_decl = 5
    RULE_array_decl = 6
    RULE_type = 7
    RULE_primitive_type = 8
    RULE_relationship = 9
    RULE_ignored_class_decl = 10
    RULE_generic_text = 11

    ruleNames =  [ "stateFile", "element", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl", "array_decl", "type", "primitive_type", "relationship", 
                   "ignored_class_decl", "generic_text" ]

    EOF = Token.EOF
    CLASS_DIAGRAM=1
    CLASS=2
    CONSTANT=3
    VARIABLE=4
    ARRAY=5
    NOTE=6
    BIT=7
    BOOL=8
    BYTE=9
    INT=10
    SHORT=11
    ARROW=12
    LCURLY=13
    RCURLY=14
    LBRACKET=15
    RBRACKET=16
    DOT=17
    SLASH=18
    DASH=19
    COMMA=20
    ID=21
    COMMENT=22
    WS=23

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StateFileContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def CLASS_DIAGRAM(self):
            return self.getToken(StateMmdParser.CLASS_DIAGRAM, 0)

        def EOF(self):
            return self.getToken(StateMmdParser.EOF, 0)

        def element(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateMmdParser.ElementContext)
            else:
                return self.getTypedRuleContext(StateMmdParser.ElementContext,i)


        def getRuleIndex(self):
            return StateMmdParser.RULE_stateFile

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStateFile" ):
                listener.enterStateFile(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStateFile" ):
                listener.exitStateFile(self)




    def stateFile(self):

        localctx = StateMmdParser.StateFileContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_stateFile)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 24
            self.match(StateMmdParser.CLASS_DIAGRAM)
            self.state = 28
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2 or _la==21:
                self.state = 25
                self.element()
                self.state = 30
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 31
            self.match(StateMmdParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ElementContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def enum_type_decl(self):
            return self.getTypedRuleContext(StateMmdParser.Enum_type_declContext,0)


        def const_var_decl(self):
            return self.getTypedRuleContext(StateMmdParser.Const_var_declContext,0)


        def array_decl(self):
            return self.getTypedRuleContext(StateMmdParser.Array_declContext,0)


        def var_decl(self):
            return self.getTypedRuleContext(StateMmdParser.Var_declContext,0)


        def relationship(self):
            return self.getTypedRuleContext(StateMmdParser.RelationshipContext,0)


        def ignored_class_decl(self):
            return self.getTypedRuleContext(StateMmdParser.Ignored_class_declContext,0)


        def getRuleIndex(self):
            return StateMmdParser.RULE_element

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterElement" ):
                listener.enterElement(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitElement" ):
                listener.exitElement(self)




    def element(self):

        localctx = StateMmdParser.ElementContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_element)
        try:
            self.state = 39
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,1,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 33
                self.enum_type_decl()
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 34
                self.const_var_decl()
                pass

            elif la_ == 3:
                self.enterOuterAlt(localctx, 3)
                self.state = 35
                self.array_decl()
                pass

            elif la_ == 4:
                self.enterOuterAlt(localctx, 4)
                self.state = 36
                self.var_decl()
                pass

            elif la_ == 5:
                self.enterOuterAlt(localctx, 5)
                self.state = 37
                self.relationship()
                pass

            elif la_ == 6:
                self.enterOuterAlt(localctx, 6)
                self.state = 38
                self.ignored_class_decl()
                pass


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

        def CLASS(self):
            return self.getToken(StateMmdParser.CLASS, 0)

        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def LCURLY(self):
            return self.getToken(StateMmdParser.LCURLY, 0)

        def id_set(self):
            return self.getTypedRuleContext(StateMmdParser.Id_setContext,0)


        def RCURLY(self):
            return self.getToken(StateMmdParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateMmdParser.RULE_enum_type_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterEnum_type_decl" ):
                listener.enterEnum_type_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitEnum_type_decl" ):
                listener.exitEnum_type_decl(self)




    def enum_type_decl(self):

        localctx = StateMmdParser.Enum_type_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_enum_type_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 41
            self.match(StateMmdParser.CLASS)
            self.state = 42
            self.match(StateMmdParser.ID)
            self.state = 43
            self.match(StateMmdParser.LCURLY)
            self.state = 44
            self.id_set()
            self.state = 45
            self.match(StateMmdParser.RCURLY)
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
                return self.getTokens(StateMmdParser.ID)
            else:
                return self.getToken(StateMmdParser.ID, i)

        def primitive_type(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateMmdParser.Primitive_typeContext)
            else:
                return self.getTypedRuleContext(StateMmdParser.Primitive_typeContext,i)


        def getRuleIndex(self):
            return StateMmdParser.RULE_id_set

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterId_set" ):
                listener.enterId_set(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitId_set" ):
                listener.exitId_set(self)




    def id_set(self):

        localctx = StateMmdParser.Id_setContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_id_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 49 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 49
                self._errHandler.sync(self)
                token = self._input.LA(1)
                if token in [21]:
                    self.state = 47
                    self.match(StateMmdParser.ID)
                    pass
                elif token in [7, 8, 9, 10, 11]:
                    self.state = 48
                    self.primitive_type()
                    pass
                else:
                    raise NoViableAltException(self)

                self.state = 51 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not ((((_la) & ~0x3f) == 0 and ((1 << _la) & 2101120) != 0)):
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

        def CLASS(self):
            return self.getToken(StateMmdParser.CLASS, 0)

        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def LCURLY(self):
            return self.getToken(StateMmdParser.LCURLY, 0)

        def CONSTANT(self):
            return self.getToken(StateMmdParser.CONSTANT, 0)

        def type_(self):
            return self.getTypedRuleContext(StateMmdParser.TypeContext,0)


        def RCURLY(self):
            return self.getToken(StateMmdParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateMmdParser.RULE_const_var_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterConst_var_decl" ):
                listener.enterConst_var_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitConst_var_decl" ):
                listener.exitConst_var_decl(self)




    def const_var_decl(self):

        localctx = StateMmdParser.Const_var_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_const_var_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 53
            self.match(StateMmdParser.CLASS)
            self.state = 54
            self.match(StateMmdParser.ID)
            self.state = 55
            self.match(StateMmdParser.LCURLY)
            self.state = 56
            self.match(StateMmdParser.CONSTANT)
            self.state = 57
            self.type_()
            self.state = 58
            self.match(StateMmdParser.RCURLY)
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

        def CLASS(self):
            return self.getToken(StateMmdParser.CLASS, 0)

        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def LCURLY(self, i:int=None):
            if i is None:
                return self.getTokens(StateMmdParser.LCURLY)
            else:
                return self.getToken(StateMmdParser.LCURLY, i)

        def VARIABLE(self):
            return self.getToken(StateMmdParser.VARIABLE, 0)

        def type_(self):
            return self.getTypedRuleContext(StateMmdParser.TypeContext,0)


        def RCURLY(self, i:int=None):
            if i is None:
                return self.getTokens(StateMmdParser.RCURLY)
            else:
                return self.getToken(StateMmdParser.RCURLY, i)

        def id_set(self):
            return self.getTypedRuleContext(StateMmdParser.Id_setContext,0)


        def getRuleIndex(self):
            return StateMmdParser.RULE_var_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterVar_decl" ):
                listener.enterVar_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitVar_decl" ):
                listener.exitVar_decl(self)




    def var_decl(self):

        localctx = StateMmdParser.Var_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_var_decl)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 60
            self.match(StateMmdParser.CLASS)
            self.state = 61
            self.match(StateMmdParser.ID)
            self.state = 62
            self.match(StateMmdParser.LCURLY)
            self.state = 63
            self.match(StateMmdParser.VARIABLE)
            self.state = 64
            self.type_()
            self.state = 69
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==13:
                self.state = 65
                self.match(StateMmdParser.LCURLY)
                self.state = 66
                self.id_set()
                self.state = 67
                self.match(StateMmdParser.RCURLY)


            self.state = 71
            self.match(StateMmdParser.RCURLY)
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

        def CLASS(self):
            return self.getToken(StateMmdParser.CLASS, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateMmdParser.ID)
            else:
                return self.getToken(StateMmdParser.ID, i)

        def LCURLY(self):
            return self.getToken(StateMmdParser.LCURLY, 0)

        def ARRAY(self):
            return self.getToken(StateMmdParser.ARRAY, 0)

        def primitive_type(self):
            return self.getTypedRuleContext(StateMmdParser.Primitive_typeContext,0)


        def LBRACKET(self):
            return self.getToken(StateMmdParser.LBRACKET, 0)

        def RBRACKET(self):
            return self.getToken(StateMmdParser.RBRACKET, 0)

        def RCURLY(self):
            return self.getToken(StateMmdParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateMmdParser.RULE_array_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterArray_decl" ):
                listener.enterArray_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitArray_decl" ):
                listener.exitArray_decl(self)




    def array_decl(self):

        localctx = StateMmdParser.Array_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_array_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 73
            self.match(StateMmdParser.CLASS)
            self.state = 74
            self.match(StateMmdParser.ID)
            self.state = 75
            self.match(StateMmdParser.LCURLY)
            self.state = 76
            self.match(StateMmdParser.ARRAY)
            self.state = 77
            self.primitive_type()
            self.state = 78
            self.match(StateMmdParser.LBRACKET)
            self.state = 79
            self.match(StateMmdParser.ID)
            self.state = 80
            self.match(StateMmdParser.RBRACKET)
            self.state = 81
            self.match(StateMmdParser.RCURLY)
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
            return self.getTypedRuleContext(StateMmdParser.Primitive_typeContext,0)


        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def getRuleIndex(self):
            return StateMmdParser.RULE_type

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterType" ):
                listener.enterType(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitType" ):
                listener.exitType(self)




    def type_(self):

        localctx = StateMmdParser.TypeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_type)
        try:
            self.state = 85
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [7, 8, 9, 10, 11]:
                self.enterOuterAlt(localctx, 1)
                self.state = 83
                self.primitive_type()
                pass
            elif token in [21]:
                self.enterOuterAlt(localctx, 2)
                self.state = 84
                self.match(StateMmdParser.ID)
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
            return self.getToken(StateMmdParser.BIT, 0)

        def BOOL(self):
            return self.getToken(StateMmdParser.BOOL, 0)

        def BYTE(self):
            return self.getToken(StateMmdParser.BYTE, 0)

        def INT(self):
            return self.getToken(StateMmdParser.INT, 0)

        def SHORT(self):
            return self.getToken(StateMmdParser.SHORT, 0)

        def getRuleIndex(self):
            return StateMmdParser.RULE_primitive_type

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterPrimitive_type" ):
                listener.enterPrimitive_type(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitPrimitive_type" ):
                listener.exitPrimitive_type(self)




    def primitive_type(self):

        localctx = StateMmdParser.Primitive_typeContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_primitive_type)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 87
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 3968) != 0)):
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


    class RelationshipContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def ARROW(self):
            return self.getToken(StateMmdParser.ARROW, 0)

        def type_(self):
            return self.getTypedRuleContext(StateMmdParser.TypeContext,0)


        def getRuleIndex(self):
            return StateMmdParser.RULE_relationship

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterRelationship" ):
                listener.enterRelationship(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitRelationship" ):
                listener.exitRelationship(self)




    def relationship(self):

        localctx = StateMmdParser.RelationshipContext(self, self._ctx, self.state)
        self.enterRule(localctx, 18, self.RULE_relationship)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 89
            self.match(StateMmdParser.ID)
            self.state = 90
            self.match(StateMmdParser.ARROW)
            self.state = 91
            self.type_()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Ignored_class_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def CLASS(self):
            return self.getToken(StateMmdParser.CLASS, 0)

        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def LCURLY(self):
            return self.getToken(StateMmdParser.LCURLY, 0)

        def NOTE(self):
            return self.getToken(StateMmdParser.NOTE, 0)

        def RCURLY(self):
            return self.getToken(StateMmdParser.RCURLY, 0)

        def generic_text(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateMmdParser.Generic_textContext)
            else:
                return self.getTypedRuleContext(StateMmdParser.Generic_textContext,i)


        def getRuleIndex(self):
            return StateMmdParser.RULE_ignored_class_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterIgnored_class_decl" ):
                listener.enterIgnored_class_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitIgnored_class_decl" ):
                listener.exitIgnored_class_decl(self)




    def ignored_class_decl(self):

        localctx = StateMmdParser.Ignored_class_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 20, self.RULE_ignored_class_decl)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 93
            self.match(StateMmdParser.CLASS)
            self.state = 94
            self.match(StateMmdParser.ID)
            self.state = 95
            self.match(StateMmdParser.LCURLY)
            self.state = 96
            self.match(StateMmdParser.NOTE)
            self.state = 100
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & 4063232) != 0):
                self.state = 97
                self.generic_text()
                self.state = 102
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 103
            self.match(StateMmdParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Generic_textContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self):
            return self.getToken(StateMmdParser.ID, 0)

        def DOT(self):
            return self.getToken(StateMmdParser.DOT, 0)

        def SLASH(self):
            return self.getToken(StateMmdParser.SLASH, 0)

        def DASH(self):
            return self.getToken(StateMmdParser.DASH, 0)

        def COMMA(self):
            return self.getToken(StateMmdParser.COMMA, 0)

        def getRuleIndex(self):
            return StateMmdParser.RULE_generic_text

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterGeneric_text" ):
                listener.enterGeneric_text(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitGeneric_text" ):
                listener.exitGeneric_text(self)




    def generic_text(self):

        localctx = StateMmdParser.Generic_textContext(self, self._ctx, self.state)
        self.enterRule(localctx, 22, self.RULE_generic_text)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 105
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & 4063232) != 0)):
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





