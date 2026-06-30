/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

/**
 * A FEEL 1.1 grammar for ANTLR 4 based on the DMN Language Specification
 * chapter 10.
 *
 * NOTE: This grammar was created out of the Java 8 feel11 available with
 *       ANTLR 4 source code.
 *
 */
grammar FeelExpr;

/**************************
 *       EXPRESSIONS
 **************************/
compilation_unit
    : expression EOF
    ;

// #1
expression
    : textualExpression  #expressionTextual
    ;

// #2
textualExpression
    : functionDefinition
    | conditionalOrExpression
    ;

// #41
parameters
    : LPAREN RPAREN                       #parametersEmpty
    | LPAREN namedParameters RPAREN       #parametersNamed
    | LPAREN positionalParameters RPAREN  #parametersPositional
    ;

// #42 #43
namedParameters
    : namedParameter (COMMA namedParameter)*
    ;

namedParameter
    : nameDefinition COLON expression
    ;

// #44
positionalParameters
    : expression ( COMMA expression )*
    ;

// #46
forExpression
    : FOR iterationContexts RETURN expression
    ;

iterationContexts
    : iterationContext ( COMMA iterationContext )*
    ;

iterationContext
    : iterationNameDefinition IN expression '..' expression
    | iterationNameDefinition IN expression
    ;

// #47
ifExpression
    : IF expression THEN expression ELSE expression
    ;

// #48
quantifiedExpression
    : SOME iterationContexts SATISFIES expression    #quantExprSome
    | EVERY iterationContexts SATISFIES expression   #quantExprEvery
    ;

// #54
type
    : Identifier LT type GT                                                     #listType
    | Identifier LT type GT                                                     #rangeType
    | Identifier LT Identifier COLON type ( COMMA Identifier COLON type )* GT   #contextType
    | FUNCTION                                                                  #qnType
    | FUNCTION LT (type ( COMMA type )*)? GT RARROW type                        #functionType
    | qualifiedName                                                             #qnType
    ;

// #56
list
    : LBRACK RBRACK
    | LBRACK expressionList RBRACK
    ;

// #57
functionDefinition
    : FUNCTION LPAREN formalParameters? RPAREN EXTERNAL? expression
    ;

formalParameters
    : formalParameter ( COMMA formalParameter )*
    ;

// #58
formalParameter
    : nameDefinition COLON type
    | nameDefinition
    ;

// #59
context
    : LBRACE RBRACE
    | LBRACE contextEntries RBRACE
    ;

contextEntries
    : contextEntry ( COMMA contextEntry )*
    ;

// #60
contextEntry
    : key COLON expression
    ;

// #61
key
    : nameDefinition   #keyName
    | StringLiteral    #keyString
    ;

nameDefinition
    : nameDefinitionTokens
    ;

nameDefinitionWithEOF
    : nameDefinition EOF
    ;

nameDefinitionTokens
    : Identifier
        ( Identifier
        | additionalNameSymbol
        | IntegerLiteral
        | FloatingPointLiteral
        | reusableKeywords
        | IN
        )*
    ;

iterationNameDefinition
    : iterationNameDefinitionTokens
    ;

iterationNameDefinitionTokens
    : Identifier
        ( Identifier
        | additionalNameSymbol
        | IntegerLiteral
        | FloatingPointLiteral
        | reusableKeywords
        )*
    ;


additionalNameSymbol
    : DOT | DIV | SUB | ADD | MUL | QUOTE
    ;

conditionalOrExpression
    :  conditionalXOrExpression                              #condOrXor
    |  conditionalOrExpression OR conditionalXOrExpression   #condOr
    ;

conditionalXOrExpression
    : conditionalAndExpression                                 #condXorAnd
    | conditionalXOrExpression XOR conditionalAndExpression    #condXOr
    ;

conditionalAndExpression
    :   comparisonExpression                                   #condAndComp
    |   conditionalAndExpression AND comparisonExpression      #condAnd
    ;

comparisonExpression
    :   relationalExpression                                           #compExpressionRel
    |   comparisonExpression (LT |
                                      GT |
                                      LE |
                                      GE |
                                      EQUAL |
                                      NOTEQUAL) relationalExpression   #compExpression
    ;

relationalExpression
    :   additiveExpression                                                       #relExpressionAdd
    |   relationalExpression BETWEEN additiveExpression AND additiveExpression   #relExpressionBetween
    |   relationalExpression IN LPAREN positiveUnaryTests RPAREN                 #relExpressionTestList
    |   relationalExpression IN expression                                       #relExpressionValue
    |   relationalExpression INSTANCE OF type                                    #relExpressionInstanceOf
    ;

expressionList
    :   expression  (COMMA expression)*
    ;

additiveExpression
    :   multiplicativeExpression                         #addExpressionMult
    |   additiveExpression ADD multiplicativeExpression  #addExpression
    |   additiveExpression SUB multiplicativeExpression  #addExpression
    ;

multiplicativeExpression
    :   powerExpression                                           #multExpressionPow
    |   multiplicativeExpression ( MUL | DIV ) powerExpression    #multExpression
    ;

powerExpression
    :   pathDescendantFilterExpression                       #powExpressionUnary
    |   powerExpression POW pathDescendantFilterExpression   #powExpression
    ;

// FEEL Grammar (2.g) (Path, Descendant, and Filter Expressions)
pathDescendantFilterExpression
    :   unaryExpression
    // #50 Filter Expression
    |   pathDescendantFilterExpression LBRACK expression RBRACK
    // #43 Path Expression
    |   pathDescendantFilterExpression DOT qualifiedName
    // #68 Descendant Expression
    |   pathDescendantFilterExpression SPREAD qualifiedName
    ;

unaryExpression
    :   unaryExpression parameters               #fnInvocation
    |   SUB unaryExpression                      #signedUnaryExpressionMinus
    |   unaryExpressionNotPlusMinus              #nonSignedUnaryExpression
    |   ADD unaryExpressionNotPlusMinus          #signedUnaryExpressionPlus
    ;

unaryExpressionNotPlusMinus
    : primary (DOT qualifiedName parameters? )?   #uenpmPrimary
    ;

chooseExpression
    : CHOOSE list
    ;

tripleExpression
    : LPAREN qualifiedName COMMA list COMMA expression RPAREN    #tripExpression
    ;

primary
    : literal                     #primaryLiteral
    | forExpression               #primaryForExpression
    | quantifiedExpression        #primaryQuantifiedExpression
    | ifExpression                #primaryIfExpression
    | tripleExpression            #primaryTripleExpression
    | interval                    #primaryInterval
    | list                        #primaryList
    | context                     #primaryContext
    | chooseExpression            #primaryChoose
    | LPAREN expression RPAREN    #primaryParens
    | simplePositiveUnaryTest     #primaryUnaryTest
    | qualifiedName               #primaryName
    ;

// #33 - #39
literal
    :   IntegerLiteral          #numberLiteral
    |   FloatingPointLiteral    #numberLiteral
    |   BooleanLiteral          #boolLiteral
    |   atLiteral               #atLiteralLabel
    |   StringLiteral           #stringLiteral
    |   NULL                    #nullLiteral
    |   UNDEFINEDVALUE          #undefined
    ;

atLiteral
    : AT atLiteralValue
    ;

atLiteralValue
    : StringLiteral
    ;

BooleanLiteral
    :   TRUE
    |   FALSE
    ;


/**************************
 *    OTHER CONSTRUCTS
 **************************/

// #7
simplePositiveUnaryTest
    : LT endpoint         #positiveUnaryTestIneqInterval
    | GT endpoint         #positiveUnaryTestIneqInterval
    | LE endpoint         #positiveUnaryTestIneqInterval
    | GE endpoint         #positiveUnaryTestIneqInterval
    | EQUAL endpoint      #positiveUnaryTestIneqInterval
    | NOTEQUAL endpoint   #positiveUnaryTestIneq
    | interval            #positiveUnaryTestInterval
    ;


// #13
simplePositiveUnaryTests
    : simplePositiveUnaryTest ( COMMA simplePositiveUnaryTest )*
    ;


// #14
simpleUnaryTests
    : simplePositiveUnaryTests                     #positiveSimplePositiveUnaryTests
    | NOT LPAREN simplePositiveUnaryTests RPAREN   #negatedSimplePositiveUnaryTests
    | SUB                                          #positiveUnaryTestDash
    ;

// #15
positiveUnaryTest
    : expression
    ;

// #16
positiveUnaryTests
    : positiveUnaryTest ( COMMA positiveUnaryTest )*
    ;


unaryTestsRoot
    : unaryTests EOF
    ;

// #17 (root for decision tables)
unaryTests
    :
    NOT LPAREN positiveUnaryTests RPAREN #unaryTests_negated
    | positiveUnaryTests                 #unaryTests_positive
    | SUB                                #unaryTests_empty
    ;

// #18
endpoint
    : additiveExpression
    ;

// #8-#12
interval
    : LPAREN endpoint ELIPSIS endpoint RPAREN
    | LPAREN endpoint ELIPSIS endpoint LBRACK
    | LPAREN endpoint ELIPSIS endpoint RBRACK
    | RBRACK endpoint ELIPSIS endpoint RPAREN
    | RBRACK endpoint ELIPSIS endpoint LBRACK
    | RBRACK endpoint ELIPSIS endpoint RBRACK
    | LBRACK endpoint ELIPSIS endpoint RPAREN
    | LBRACK endpoint ELIPSIS endpoint LBRACK
    | LBRACK endpoint ELIPSIS endpoint RBRACK
    ;

// #20
qualifiedName
    : nameRef (DOT nameRef)*
    ;

nameRef
    : ( Identifier | NOT ) nameRefOtherToken*
    ;

nameRefOtherToken
    : ~(LPAREN|RPAREN|LBRACK|RBRACK|LBRACE|RBRACE|LT|GT|EQUAL|BANG|COMMA)
    ;

/********************************
 *      KEYWORDS
 ********************************/
reusableKeywords
    : FOR
    | RETURN
    | IF
    | THEN
    | ELSE
    | SOME
    | EVERY
    | CHOOSE
    | SATISFIES
    | INSTANCE
    | OF
    | FUNCTION
    | EXTERNAL
    | OR
    | AND
    | XOR
    | BETWEEN
    | NOT
    | NULL
    | UNDEFINEDVALUE
    | TRUE
    | FALSE
    ;

FOR
    : 'for'
    ;

RETURN
    : 'return'
    ;

// can't be reused
IN
    : 'in'
    ;

IF
    : 'if'
    ;

THEN
    : 'then'
    ;

ELSE
    : 'else'
    ;

SOME
    : 'some'
    ;

EVERY
    : 'every'
    ;

CHOOSE
    : 'choose'
    ;

SATISFIES
    : 'satisfies'
    ;

INSTANCE
    : 'instance'
    ;

OF
    : 'of'
    ;

FUNCTION
    : 'function'
    ;

EXTERNAL
    : 'external'
    ;

OR
    : 'or'
    ;

AND
    : 'and'
    ;

XOR
    : 'Xor'
    ;

BETWEEN
    : 'between'
    ;

NULL
    : 'null'
    ;

UNDEFINEDVALUE
    : 'undefined'
    ;

TRUE
    : 'true'
    ;

FALSE
    : 'false'
    ;

QUOTE
    :
    '\''
    ;

/********************************
 *      LEXER RULES
 *
 * Include:
 *      - number literals
 *      - boolean literals
 *      - string literals
 *      - null literal
 ********************************/

// Number Literals

// #37
IntegerLiteral
    :   DecimalIntegerLiteral
    |   HexIntegerLiteral
    ;

fragment
DecimalIntegerLiteral
    :   DecimalNumeral IntegerTypeSuffix?
    ;

fragment
HexIntegerLiteral
    :   HexNumeral IntegerTypeSuffix?
    ;

fragment
IntegerTypeSuffix
    :   [lL]
    ;

fragment
DecimalNumeral
    :   Digit (Digits? | Underscores Digits)
    ;

fragment
Digits
    :   Digit (DigitsAndUnderscores? Digit)?
    ;

fragment
Digit
    :   [0-9]
    ;

fragment
NonZeroDigit
    :   [1-9]
    ;

fragment
DigitsAndUnderscores
    :   DigitOrUnderscore+
    ;

fragment
DigitOrUnderscore
    :   Digit
    |   '_'
    ;

fragment
Underscores
    :   '_'+
    ;

fragment
HexNumeral
    :   '0' [xX] HexDigits
    ;

fragment
HexDigits
    :   HexDigit (HexDigitsAndUnderscores? HexDigit)?
    ;

fragment
HexDigit
    :   [0-9a-fA-F]
    ;

fragment
HexDigitsAndUnderscores
    :   HexDigitOrUnderscore+
    ;

fragment
HexDigitOrUnderscore
    :   HexDigit
    |   '_'
    ;

// #37
FloatingPointLiteral
    :   DecimalFloatingPointLiteral
    |   HexadecimalFloatingPointLiteral
    ;

fragment
DecimalFloatingPointLiteral
    :   Digits '.' Digits ExponentPart? FloatTypeSuffix?
    |   '.' Digits ExponentPart? FloatTypeSuffix?
    |   Digits ExponentPart FloatTypeSuffix?
    |   Digits FloatTypeSuffix
    ;

fragment
ExponentPart
    :   ExponentIndicator SignedInteger
    ;

fragment
ExponentIndicator
    :   [eE]
    ;

fragment
SignedInteger
    :   Sign? Digits
    ;

fragment
Sign
    :   [+-]
    ;

fragment
FloatTypeSuffix
    :   [fFdD]
    ;

fragment
HexadecimalFloatingPointLiteral
    :   HexSignificand BinaryExponent FloatTypeSuffix?
    ;

fragment
HexSignificand
    :   HexNumeral '.'?
    |   '0' [xX] HexDigits? '.' HexDigits
    ;

fragment
BinaryExponent
    :   BinaryExponentIndicator SignedInteger
    ;

fragment
BinaryExponentIndicator
    :   [pP]
    ;

// String Literals

StringLiteral
    :   '"' StringCharacters? '"'
    ;

fragment
StringCharacters
    :   StringCharacter+
    ;

fragment
StringCharacter
    :   ~["\\]
    |   EscapeSequence
    ;

// Escape Sequences for Character and String Literals

fragment
EscapeSequence
    :   '\\' ~[u]     // required to support FEEL regexps
    |   UnicodeEscape // This is not in the spec but prevents having to preprocess the input
    ;

fragment
ZeroToThree
    :   [0-3]
    ;

// This is not in the spec but prevents having to preprocess the input
fragment
UnicodeEscape
    :   '\\' 'U' HexDigit HexDigit HexDigit HexDigit HexDigit HexDigit
    |   '\\' 'u' HexDigit HexDigit HexDigit HexDigit
    ;

// The Null Literal

// Separators

LPAREN : '(';
RPAREN : ')';
LBRACE : '{';
RBRACE : '}';
LBRACK : '[';
RBRACK : ']';
COMMA : ',';
ELIPSIS : '..';
DOT : '.';
SPREAD : '...';

// Operators

EQUAL : '=';
GT : '>';
LT : '<';
LE : '<=';
GE : '>=';
NOTEQUAL : '!=';

COLON : ':';

RARROW : '->';

POW : '**';
ADD : '+';
SUB : '-';
MUL : '*';
DIV : '/';
BANG
    : '!'
    ;

NOT
    : 'not'
    ;

AT  : '@';

Identifier
    : NameStartChar NameStartCharOrPart*
    ;

fragment
NameStartChar
    : '?' | [A-Z] | '_' | [a-z] | [\u00C0-\u00D6] | [\u00D8-\u00F6] | [\u00F8-\u02FF] | [\u0370-\u037D] | [\u037F-\u1FFF] |
    [\u200C-\u200D] | [\u2070-\u218F] | [\u2C00-\u2FEF] | [\u3001-\uD7FF] | [\uF900-\uFDCF] | [\uFDF0-\uFFFD] |
    [\u{10000}-\u{EFFFF}];

fragment
NameStartCharOrPart
    : '?' | [A-Z] | '_' | [a-z] | [\u00C0-\u00D6] | [\u00D8-\u00F6] | [\u00F8-\u02FF] | [\u0370-\u037D] | [\u037F-\u1FFF] |
    [\u200C-\u200D] | [\u2070-\u218F] | [\u2C00-\u2FEF] | [\u3001-\uD7FF] | [\uF900-\uFDCF] | [\uFDF0-\uFFFD] |
    [\u{10000}-\u{EFFFF}]
    | [0-9] | '\u00B7' | [\u0300-\u036F] | [\u203F-\u2040]
    ;

//
// Whitespace and comments
//

WS  :  [ \t\r\n\u000C\u00A0]+ -> skip
    ;

COMMENT
    :   '/*' .*? '*/' -> skip
    ;

LINE_COMMENT
    :   '//' ~[\r\n]* -> skip
    ;

ANY_OTHER_CHAR
    : ~[ \t\r\n\u000c]
    ;
