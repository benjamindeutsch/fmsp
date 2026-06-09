type token =
  | CHOICE
  | STAR
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | BAR
  | SEMI
  | NEW
  | OUT
  | IN
  | IDENT of (
# 51 "piparser.mly"
        Piptree.ident
# 18 "piparser.mli"
)
  | STRING of (
# 52 "piparser.mly"
        Piptree.ident
# 23 "piparser.mli"
)
  | INT of (
# 53 "piparser.mly"
        int
# 28 "piparser.mli"
)
  | REPL
  | IF
  | THEN
  | ELSE
  | EQUAL
  | FUN
  | EQUATION
  | REDUCTION
  | PREDICATE
  | PROCESS
  | SLASH
  | DOT
  | EOF
  | LET
  | QUERY
  | BEFORE
  | PUTBEGIN
  | NONINTERF
  | EVENT
  | NOT
  | ELIMTRUE
  | FREE
  | SUCHTHAT
  | CLAUSES
  | RED
  | EQUIV
  | EQUIVEQ
  | WEDGE
  | DIFF
  | COLON
  | NOUNIF
  | PHASE
  | BARRIER
  | AMONG
  | WEAKSECRET
  | CANTEXT
  | FAIL
  | WHERE
  | OTHERWISE
  | DATA
  | PARAM
  | PRIVATE

val all :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Piptree.decl list * Piptree.process
