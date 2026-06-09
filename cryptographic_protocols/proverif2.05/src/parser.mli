type token =
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | SEMI
  | COLON
  | IDENT of (
# 46 "parser.mly"
        Ptree.ident
# 13 "parser.mli"
)
  | INT of (
# 47 "parser.mly"
        int
# 18 "parser.mli"
)
  | RED
  | EQUIV
  | EQUIVEQ
  | EQUAL
  | FUN
  | EQUATION
  | QUERY
  | NOUNIF
  | SLASH
  | STAR
  | DOT
  | WEDGE
  | EOF
  | NOT
  | ELIMTRUE
  | DIFF
  | PREDICATE
  | REDUCTION
  | DATA
  | PARAM
  | CLAUSES
  | CONST
  | SET
  | NAME
  | TYPE
  | FORALL
  | SELECT
  | MINUS

val all :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ptree.decl list
val tall :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ptree.tdecl list
