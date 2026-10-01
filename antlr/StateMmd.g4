grammar StateMmd;

// A Mermaid state file is a class diagram. The class blocks carry the
// declarations from state.txt and the arrows at the end repeat their types.
// Comments and whitespace are ignored by the lexer, so declarations may be
// grouped in any order and separated by Mermaid comments.

stateFile
  : CLASS_DIAGRAM element* EOF
  ;

element
  : enum_type_decl
  | const_var_decl
  | array_decl
  | var_decl
  | relationship
  | ignored_class_decl
  ;

enum_type_decl
  : CLASS ID LCURLY id_set RCURLY
  ;

id_set
  : (ID | primitive_type)+
  ;

const_var_decl
  : CLASS ID LCURLY CONSTANT type RCURLY
  ;

var_decl
  : CLASS ID LCURLY VARIABLE type (LCURLY id_set RCURLY)? RCURLY
  ;

array_decl
  : CLASS ID LCURLY ARRAY primitive_type LBRACKET ID RBRACKET RCURLY
  ;

type
  : primitive_type
  | ID
  ;

primitive_type
  : BIT
  | BOOL
  | BYTE
  | INT
  | SHORT
  ;

relationship
  : ID ARROW type
  ;

// Some generated state diagrams include a prose/documentation class. It is
// syntactically valid Mermaid but is not part of the State model.
ignored_class_decl
  : CLASS ID LCURLY NOTE generic_text* RCURLY
  ;

generic_text
  : ID
  | DOT
  | SLASH
  | DASH
  | COMMA
  ;

// ---------------------------------------------------------------------------
// Lexer Rules
// ---------------------------------------------------------------------------

CLASS_DIAGRAM
  : 'classDiagram'
  ;

CLASS
  : 'class'
  ;

CONSTANT
  : '<<constant>>'
  ;

VARIABLE
  : '<<variable>>'
  ;

ARRAY
  : '<<array>>'
  ;

NOTE
  : '<<' ~[>\r\n]* '>>'
  ;

BIT
  : 'bit'
  ;

BOOL
  : 'bool'
  ;

BYTE
  : 'byte'
  ;

INT
  : 'int'
  ;

SHORT
  : 'short'
  ;

ARROW
  : '-->'
  ;

LCURLY
  : '{'
  ;

RCURLY
  : '}'
  ;

LBRACKET
  : '['
  ;

RBRACKET
  : ']'
  ;

DOT
  : '.'
  ;

SLASH
  : '/'
  ;

DASH
  : '-'
  ;

COMMA
  : ','
  ;

ID
  : [a-zA-Z0-9_]+
  ;

COMMENT
  : '%%' ~[\r\n]* -> skip
  ;

WS
  : [ \t\n\r]+ -> skip
  ;
