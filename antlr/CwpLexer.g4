lexer grammar CwpLexer;

STATEDIAGRAM : 'stateDiagram-v2' ;
STATE        : 'state' ;
AS           : 'as' ;
ARROW        : '-->' ;
COLON        : ':' -> pushMode(EXPR_MODE) ;
STRING       : '"' ~["\r\n]* '"' ;
ID           : [a-zA-Z_][a-zA-Z0-9_]* ;
COMMENT      : '%%' ~[\r\n]* -> skip ;
WS           : [ \t]+ -> skip ;
NEWLINE      : '\r'? '\n' -> skip ;

mode EXPR_MODE;
EXPR_TEXT    : ~[\r\n]+ -> popMode ;
EXPR_NL      : '\r'? '\n' -> popMode, skip ;
