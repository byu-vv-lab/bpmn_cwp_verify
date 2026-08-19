grammar Cwp;

diagram
    : header stateDecl* edgeTransition* EOF
    ;

header
    : STATEDIAGRAM
    ;

stateDecl
    : STATE STRING AS ID
    ;

edgeTransition
    : ID ARROW ID EXPR_CLAUSE?
    ;

STATEDIAGRAM : 'stateDiagram-v2' ;
STATE        : 'state' ;
AS           : 'as' ;
ARROW        : '-->' ;
STRING       : '"' ~["\r\n]* '"' ;
ID           : [a-zA-Z_][a-zA-Z0-9_]* ;
EXPR_CLAUSE  : ':' [ \t]* ~[\r\n]* ;
COMMENT      : '%%' ~[\r\n]* -> skip ;
WS           : [ \t]+ -> skip ;
NEWLINE      : '\r'? '\n' -> skip ;
