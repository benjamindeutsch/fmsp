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
  | AT
  | IDENT of (
# 92 "pitparser.mly"
        Pitptree.ident
# 19 "pitparser.mli"
)
  | TAG of (
# 93 "pitparser.mly"
        Pitptree.ident
# 24 "pitparser.mli"
)
  | STRING of (
# 94 "pitparser.mly"
        Pitptree.ident
# 29 "pitparser.mli"
)
  | PROJECTION of (
# 95 "pitparser.mly"
        Pitptree.ident
# 34 "pitparser.mli"
)
  | UNDERSCORE of (
# 96 "pitparser.mly"
        Parsing_helper.extent
# 39 "pitparser.mli"
)
  | INT of (
# 97 "pitparser.mly"
        int
# 44 "pitparser.mli"
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
  | SELECT
  | PHASE
  | BARRIER
  | AMONG
  | WEAKSECRET
  | PARAM
  | ORTEXT
  | FAIL
  | LESS
  | GREATER
  | GEQ
  | PLUS
  | MINUS
  | TYPE
  | SET
  | FORALL
  | CONST
  | INJEVENT
  | OR
  | CHANNEL
  | LETFUN
  | DEFINE
  | EXPAND
  | YIELD
  | LEQ
  | PROBA
  | LETPROBA
  | OPTIMIF
  | ISCST
  | COUNT
  | FLOAT of (
# 161 "pitparser.mly"
          float
# 110 "pitparser.mli"
)
  | LBRACE
  | RBRACE
  | PROOF
  | IMPLEMENTATION
  | EQUIVALENCE
  | OTHERWISE
  | FOREACH
  | DO
  | SECRET
  | PUBLICVARS
  | RANDOM
  | LEFTARROW
  | POWER
  | LEMMA
  | AXIOM
  | RESTRICTION
  | FOR
  | TABLE
  | INSERT
  | GET

val all :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.tdecl list * Pitptree.tprocess_e * Pitptree.tprocess_e option
val lib :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.tdecl list
val permut :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.ident list list
val order :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.ident list
val term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Pitptree.term_e
