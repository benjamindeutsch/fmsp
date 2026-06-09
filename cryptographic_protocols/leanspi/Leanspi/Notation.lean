
namespace Notation

/-- The `Pi` typeclass defines the core π-calculus structure.

This is a polymorphic interface for different process calculi (Pi, Spi, and extensions).
-/
class Pi (Proc: Type) where
  Term  : Type
  Var  : Type
  Nam  : Type
  Typ  : Type

  mkVar : Var -> Term
  mkNam : Nam -> Term

  Stop : Proc
  In   : Term -> Var -> Typ -> Proc -> Proc
  Out  : Term -> Term -> Proc -> Proc
  New  : Nam -> Typ -> Proc -> Proc
  Par  : Proc -> Proc -> Proc
  Rep  : Proc -> Proc
  IfEq : Term -> Term -> Proc -> Proc -> Proc

/-- Interface for symmetric encryption in Spi calculus. -/
class SEnc (Proc: Type) extends Pi (Proc) where
  /-- Symmetric encryption: `⦃m⦄ˢ k` -/
  senc : Pi.Term Proc -> Pi.Term Proc -> Pi.Term Proc
  /-- Symmetric decryption -/
  SDec : Pi.Term Proc -> Pi.Var Proc -> Pi.Term Proc -> Proc -> Proc

/-- Interface for asymmetric encryption in Spi calculus. -/
class AEnc (Proc: Type) extends Pi (Proc) where
  /-- Asymmetric encryption: `⦃m⦄ᵃ k` -/
  aenc : Pi.Term Proc -> Pi.Term Proc -> Pi.Term Proc
  /-- Asymmetric decryption -/
  ADec : Pi.Term Proc -> Pi.Var Proc -> Pi.Term Proc -> Proc -> Proc

/-- Interface for digital signatures in Spi calculus. -/
class Sign (Proc: Type) extends Pi (Proc) where
  /-- Digital signature: `⟦m⟧ k` -/
  sign : Pi.Term Proc -> Pi.Term Proc -> Pi.Term Proc
  /-- Signature verification -/
  Ver : Pi.Term Proc -> Pi.Var Proc -> Pi.Term Proc -> Proc -> Proc

/-- Interface for pairs/tuples in Spi calculus. -/
class Tuple (Proc: Type) extends Pi (Proc) where
  /-- Pair construction -/
  Tuple : Pi.Term Proc -> Pi.Term Proc -> Pi.Term Proc
  /-- Project first component -/
  Fst : Pi.Term Proc -> Pi.Var Proc -> Proc -> Proc
  /-- Project second component -/
  Snd : Pi.Term Proc -> Pi.Var Proc -> Proc -> Proc

/-- Syntax category for process expressions -/
declare_syntax_cat process

/-!  # Process syntax -/
syntax "∅" : process
syntax "in" "(" term "," ident ":" term ")" (";" process)? : process
syntax "out" "(" term "," term ")" (";" process)? : process
syntax "new" ident ":" term ";" process : process
syntax:50 "if" term:60 "=" term:61  "then" process ("else" process)? : process
syntax process "|" process : process
syntax:max "!" process : process
syntax "(" process ")" : process
syntax:max "[" term:1 "]" : process
syntax:min "pi" "{"  process  "}" : term
syntax:min "pi" "(" term ")" "{" process "}" : term
syntax "let" ident ":=" term "in" process : process
syntax "case" term "of" "⦃" ident "⦄ᵃ" term "in" process : process
syntax "case" term "of" "⦃" ident "⦄ˢ" term "in" process : process
syntax "case" term "of" "⟦" ident "⟧" term "in" process : process

macro_rules
  | `(pi ($t) { $p }) => `(@id $t (pi { $p }))
  | `(pi { ∅ } ) => `(Pi.Stop)
  | `(pi { in($c, $m : $t) } ) => `(Pi.In $c $(Lean.quote m.getId.toString) $t Pi.Stop)
  | `(pi { in($c, $m : $t); $p2 } ) =>
       `(Pi.In $c $(Lean.quote m.getId.toString) $t (let $m := (Pi.mkVar $(Lean.quote m.getId.toString)); (pi { $p2 })))
  | `(pi { out($c, $m )} ) => `(Pi.Out $c $m Pi.Stop)
  | `(pi { out($c, $m ); $p2 } ) => `(Pi.Out $c $m (pi { $p2 }))
  | `(pi { new $m : $t; $p2 } ) =>
       `(Pi.New $(Lean.quote m.getId.toString) $t (let $m := (Pi.mkNam $(Lean.quote m.getId.toString)); (pi { $p2 })))
  | `(pi { $p1 | $p2 } ) => `(Pi.Par (pi { $p1 } ) (pi { $p2 }))
  | `(pi { !$p1 } ) => `(Pi.Rep (pi { $p1 }))
  | `(pi { if  $a = $b then $p1 } ) => `(Pi.IfEq $a $b (pi { $p1 }) Pi.Stop)
  | `(pi { if  $a = $b then $p1 else $p2 } ) => `(Pi.IfEq $a $b (pi { $p1 }) (pi { $p2 }))
  | `(pi { [ $p ] }) => `($p)
  | `(pi { ($p) }) => `(pi { $p })
  | `(pi { let $x := $v in $p }) => `(let $x := $v; pi { $p })
  | `(pi { case $M of ⦃ $x ⦄ˢ $K in $p}) => `(SEnc.SDec $M $(Lean.quote x.getId.toString) $K
                                                 (let $x := (Pi.mkVar $(Lean.quote x.getId.toString)); (pi { $p })))
  | `(pi { case $M of ⦃ $x ⦄ᵃ $K in $p}) => `(AEnc.ADec $M $(Lean.quote x.getId.toString) $K
                                                 (let $x := (Pi.mkVar $(Lean.quote x.getId.toString)); (pi { $p })))
  | `(pi { case $M of ⟦ $x ⟧ $K in $p}) => `(Sign.Ver $M $(Lean.quote x.getId.toString) $K
                                                 (let $x := (Pi.mkVar $(Lean.quote x.getId.toString)); (pi { $p })))


/-- Notation for symmetric encryption: `⦃m⦄ˢ k` -/
notation (name:=n_aenc) "⦃" m "⦄ᵃ" k => AEnc.aenc m k
/-- Notation for asymmetric encryption: `⦃m⦄ᵃ k` -/
notation (name:=n_senc) "⦃" m "⦄ˢ" k => SEnc.senc m k
/-- Notation for digital signature: `⟦m⟧ k` -/
notation (name:=n_sign) "⟦" m "⟧" k => Sign.sign m k
