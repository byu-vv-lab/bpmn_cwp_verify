grammar State;

state
  : (enum_type_decl)* (const_var_decl)* (array_decl)* (typedef_decl)* (var_decl)+ EOF
  ;

enum_type_decl
  : ENUM ID LCURLY id_set RCURLY
  ;

id_set
  : (ID)+
  ;

const_var_decl
  : CONST ID COLON type EQUALS ID
  ;

var_decl
  : VAR ID COLON type EQUALS ID (LCURLY id_set RCURLY)?
  ;

var_set
  : (var_decl)+
  ;

array_decl
  : ARRAY ID LBRACKET ID RBRACKET COLON primitive_type EQUALS LCURLY id_set RCURLY
  ;

typedef_decl
  : TYPEDEF ID LCURLY var_set typedef_decl_set RCURLY
  ;

typedef_decl_set
  : (typedef_decl)*
  ;

type
  : primitive_type
  | TYPEDEF
  | ID
  ;

primitive_type
  : BIT
  | BOOL
  | BYTE
  | INT
  | SHORT
  ;

// ---------------------------------------------------------------------------
// Lexer Rules
// ---------------------------------------------------------------------------

COLON
  : ':'
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

CONST
  : 'const'
  ;

ENUM
  : 'enum'
  ;

INT
  : 'int'
  ;

SHORT
  : 'short'
  ;

EQUALS
  : '='
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

VAR
  : 'var'
  ;

ARRAY
  : 'array'
  ;

TYPEDEF
  : 'typedef'
  ;

ID
  : [a-zA-Z0-9_]+
  ;

WS : [ \t\n\r]+ -> skip ;
