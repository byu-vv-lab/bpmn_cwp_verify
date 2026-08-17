parser grammar CwpParser;

options { tokenVocab = CwpLexer; }

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
    : ID ARROW ID (COLON expr)?
    ;

expr
    : EXPR_TEXT
    ;
