# Generated from antlr/Expr.g4 by ANTLR 4.13.2
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
    from typing import TextIO
else:
    from typing.io import TextIO


def serializedATN():
    return [
        4,0,18,87,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,
        6,7,6,2,7,7,7,2,8,7,8,2,9,7,9,2,10,7,10,2,11,7,11,2,12,7,12,2,13,
        7,13,2,14,7,14,2,15,7,15,2,16,7,16,2,17,7,17,1,0,1,0,1,0,1,1,1,1,
        1,1,1,2,1,2,1,3,1,3,1,4,1,4,1,4,1,5,1,5,1,5,1,6,1,6,1,6,1,7,1,7,
        1,8,1,8,1,8,1,9,1,9,1,10,1,10,1,11,1,11,1,12,1,12,1,13,1,13,1,14,
        1,14,1,15,1,15,1,16,4,16,77,8,16,11,16,12,16,78,1,17,4,17,82,8,17,
        11,17,12,17,83,1,17,1,17,0,0,18,1,1,3,2,5,3,7,4,9,5,11,6,13,7,15,
        8,17,9,19,10,21,11,23,12,25,13,27,14,29,15,31,16,33,17,35,18,1,0,
        2,4,0,48,57,65,90,95,95,97,122,3,0,9,10,13,13,32,32,88,0,1,1,0,0,
        0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,0,0,0,0,9,1,0,0,0,0,11,1,0,0,0,0,
        13,1,0,0,0,0,15,1,0,0,0,0,17,1,0,0,0,0,19,1,0,0,0,0,21,1,0,0,0,0,
        23,1,0,0,0,0,25,1,0,0,0,0,27,1,0,0,0,0,29,1,0,0,0,0,31,1,0,0,0,0,
        33,1,0,0,0,0,35,1,0,0,0,1,37,1,0,0,0,3,40,1,0,0,0,5,43,1,0,0,0,7,
        45,1,0,0,0,9,47,1,0,0,0,11,50,1,0,0,0,13,53,1,0,0,0,15,56,1,0,0,
        0,17,58,1,0,0,0,19,61,1,0,0,0,21,63,1,0,0,0,23,65,1,0,0,0,25,67,
        1,0,0,0,27,69,1,0,0,0,29,71,1,0,0,0,31,73,1,0,0,0,33,76,1,0,0,0,
        35,81,1,0,0,0,37,38,5,124,0,0,38,39,5,124,0,0,39,2,1,0,0,0,40,41,
        5,38,0,0,41,42,5,38,0,0,42,4,1,0,0,0,43,44,5,33,0,0,44,6,1,0,0,0,
        45,46,5,60,0,0,46,8,1,0,0,0,47,48,5,60,0,0,48,49,5,61,0,0,49,10,
        1,0,0,0,50,51,5,33,0,0,51,52,5,61,0,0,52,12,1,0,0,0,53,54,5,61,0,
        0,54,55,5,61,0,0,55,14,1,0,0,0,56,57,5,62,0,0,57,16,1,0,0,0,58,59,
        5,62,0,0,59,60,5,61,0,0,60,18,1,0,0,0,61,62,5,43,0,0,62,20,1,0,0,
        0,63,64,5,45,0,0,64,22,1,0,0,0,65,66,5,42,0,0,66,24,1,0,0,0,67,68,
        5,47,0,0,68,26,1,0,0,0,69,70,5,37,0,0,70,28,1,0,0,0,71,72,5,40,0,
        0,72,30,1,0,0,0,73,74,5,41,0,0,74,32,1,0,0,0,75,77,7,0,0,0,76,75,
        1,0,0,0,77,78,1,0,0,0,78,76,1,0,0,0,78,79,1,0,0,0,79,34,1,0,0,0,
        80,82,7,1,0,0,81,80,1,0,0,0,82,83,1,0,0,0,83,81,1,0,0,0,83,84,1,
        0,0,0,84,85,1,0,0,0,85,86,6,17,0,0,86,36,1,0,0,0,3,0,78,83,1,6,0,
        0
    ]

class ExprLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    T__0 = 1
    T__1 = 2
    T__2 = 3
    T__3 = 4
    T__4 = 5
    T__5 = 6
    T__6 = 7
    T__7 = 8
    T__8 = 9
    T__9 = 10
    T__10 = 11
    T__11 = 12
    T__12 = 13
    T__13 = 14
    T__14 = 15
    T__15 = 16
    ID = 17
    WS = 18

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'||'", "'&&'", "'!'", "'<'", "'<='", "'!='", "'=='", "'>'", 
            "'>='", "'+'", "'-'", "'*'", "'/'", "'%'", "'('", "')'" ]

    symbolicNames = [ "<INVALID>",
            "ID", "WS" ]

    ruleNames = [ "T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", 
                  "T__7", "T__8", "T__9", "T__10", "T__11", "T__12", "T__13", 
                  "T__14", "T__15", "ID", "WS" ]

    grammarFileName = "Expr.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


