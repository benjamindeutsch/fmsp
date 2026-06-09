import Mathlib.Data.Set.Basic
import Leanspi.Notation

namespace Spi

/-- Spi calculus terms extend Pi terms with cryptographic primitives.

Terms represent messages, keys, and encrypted values:
- `Var x`: Variable (input-bound identifier)
- `Name a`: Name (channel, resource, key)
- `Ek k`: Encryption key
- `Vk k`: Verification key
- `SEnc m k`: Symmetric encryption of m with key k: `{m}^k`
- `AEnc m k`: Asymmetric encryption of m with public key k: `{m}^Ek k`
- `Sign m k`: Digital signature of m with key k: `⟦m⟧ k`
-/
inductive Term (α β: Type): Type where
  | Var : α -> Term α β
  | Name : β -> Term α β
  | Ek (key: Term α β) : Term α β
  | Vk (key: Term α β) : Term α β
  | SEnc (m: Term α β)  (k: Term α β) : Term α β
  | AEnc (m: Term α β)  (k: Term α β) : Term α β
  | Sign (m:Term α β) (k:Term α β) : Term α β
  deriving Repr, DecidableEq

/-- Kinds of pattern matching/dedstruction in Spi calculus.

The `CaseOf` construct matches on encrypted constructs and extracts payloads.
-/
inductive Process.DesctrKind : Type where
  --- Asymmetric decryption
  | ADec
  --- Symmetric decryption
  | SDec
  --- Signature verification
  | Ver
deriving Repr, DecidableEq

/-- Spi calculus processes extend Pi processes with cryptographic operations.

Process constructors:
- `Stop`: Terminated process
- `In c x T P`: Input message on channel c, bind to variable x of type T
- `Out c m P`: Output message m on channel c
- `New a T P`: Restriction (create fresh name a of type T)
- `Par P Q`: Parallel composition
- `Rep P`: Replication (run infinite copies of P)
- `IfEq a b P Q`: Conditional: if a equals b then P else Q
- `CaseOf kind m x k P`: Pattern match on encrypted construct:
  - `case M of ⦃x⦄ˢ k in P` (symmetric decryption)
  - `case M of ⦃x⦄ᵃ k in P` (asymmetric decryption)
  - `case M of ⟦x⟧ k in P` (signature verification)
-/
inductive Process (α β τ : Type) : Type where
  | Stop
  | In (channel: Term α β) (var: α) (type: τ) : Process α β τ -> Process α β τ
  | Out (channel: Term α β) (msg: Term α β) : Process α β τ -> Process α β τ
  | New (name: β) (type: τ) : Process α β τ -> Process α β τ
  | Par : Process α β τ -> Process α β τ -> Process α β τ
  | Rep : Process α β τ -> Process α β τ
  | IfEq (a: Term α β ) (b: Term α β ) (thn: Process α β τ) (els: Process α β τ) : Process α β τ
  | CaseOf (kind: Process.DesctrKind) (m: Term α β) (x: α) (k: Term α β) : Process α β τ -> Process α β τ
  deriving Repr, DecidableEq

@[simp]
instance : Notation.Pi (Process α β τ) where
  Typ := τ
  Nam := β
  Var := α
  Term := Term α β
  mkVar := Term.Var
  mkNam := Term.Name

  Stop := Process.Stop
  In := Process.In
  Out := Process.Out
  New := Process.New
  Par := Process.Par
  Rep := Process.Rep
  IfEq := Process.IfEq

@[simp]
instance instSenc: Notation.SEnc (Process α β τ) where
  senc := Term.SEnc
  SDec := Process.CaseOf .SDec

@[simp]
instance instAenc: Notation.AEnc (Process α β τ) where
  aenc := Term.AEnc
  ADec := Process.CaseOf .ADec

@[simp]
instance instSign: Notation.Sign (Process α β τ) where
  sign := Term.Sign
  Ver := Process.CaseOf .Ver

variable [DecidableEq α] [DecidableEq β]

/-- Substitute term x with M in term T -/
@[simp]
def Term.subst (T: Term α β) (x: Term α β) (M: Term α β) : Term α β := if T = x then M else T

/-- Substitute term x with M throughout process P -/
@[simp]
def Process.subst (P: Process α β τ) (x: Term α β) (M: Term α β) : Process α β τ :=
  match P with
  | In c v t P       => In (c.subst x M) v t (P.subst x M)
  | Out c m P        => Out (c.subst x M) (m.subst x M) (P.subst x M)
  | New v t P        => New v t (P.subst x M)
  | Par P Q          => Par (P.subst x M) (Q.subst x M)
  | Rep P            => Rep (P.subst x M)
  | IfEq a b P Q     => IfEq (a.subst x M) (b.subst x M) (P.subst x M) (Q.subst x M)
  | Stop             => Stop
  | CaseOf d m v k P => CaseOf d (m.subst x M) v k (P.subst x M)

/-- Free variables of a term -/
@[simp] def Term.fv : Term α β -> Set α
  | Var a => { a } | _ => ∅
/-- Free names of a term -/
@[simp] def Term.fn : Term α β -> Set β
  | Name a => { a } | _ => ∅
/-- All free variables and names -/
@[simp] def Term.fvfn (t: Term α β) := { Term.Var v | v ∈ t.fv } ∪ { Term.Name n | n ∈ t.fn }


/-- Free variables of a process -/
@[simp]
def Process.fv : Process α β τ -> Set α
  | In c v _ P   => { x | x ∈ P.fv ∧ x ≠ v } ∪ c.fv
  | Out c m P    => P.fv ∪ c.fv ∪ m.fv
  | New _ _ P    => P.fv
  | Par P Q      => P.fv ∪ Q.fv
  | Rep P        => P.fv
  | IfEq a b P Q => P.fv ∪ Q.fv ∪ a.fv ∪ b.fv
  | Stop         => ∅
  | CaseOf _ m v k P => { x | x ∈ P.fv ∧ x ≠ v } ∪ m.fv ∪ k.fv

/-- Free names of a process -/
@[simp]
def Process.fn : Process α β τ -> Set β
  | In c _ _ P   => P.fn ∪ c.fn
  | Out c m P    => P.fn ∪ c.fn ∪ m.fn
  | New v _ P    => { x | x ∈ P.fn ∧ x ≠ v }
  | Par P Q      => P.fn ∪ Q.fn
  | Rep P        => P.fn
  | IfEq a b P Q => P.fn ∪ Q.fn ∪ a.fn ∪ b.fn
  | Stop         => ∅
  | CaseOf _ m _ k P => P.fn ∪ m.fn ∪ k.fn

/-- All free variables and names of a process -/
@[simp]
def Process.fvfn (t: Process α β τ) := { Term.Var v | v ∈ t.fv } ∪ { Term.Name n | n ∈ t.fn }

/-- Structural equivalence between processes. -/
inductive Process.Equiv : Process α β τ -> Process α β τ -> Prop
 | Refl   : Equiv P P
 | Sym    : Equiv P Q -> Equiv Q P
 | Tran   : Equiv P Q -> Equiv Q R -> Equiv P R
 | ParR   : Equiv P Q -> Equiv (P.Par R) (Q.Par R)
 | Rep    : Equiv P Q -> Equiv (P.Rep) (Q.Rep)
 | Res    : Equiv P Q -> Equiv (.New A T P) (.New A T Q)
 | Res0   : Equiv (.New A T (.Stop)) (.Stop)
 | Par0   : Equiv (P.Par .Stop) P
 | ParS   : Equiv (.Par P Q) (.Par Q P)
 | ParA   : Equiv ((Process.Par P Q).Par R) (P.Par (Q.Par R))
 | ParRep : Equiv (P.Rep) (Process.Par P (P.Rep))
 | ResS   : A ≠ B -> Equiv (.New A T (.New B T' P)) (.New B T' (.New A T P))
 | ResF   : A ∉ P.fn -> Equiv (.New A T (Process.Par P Q)) (P.Par (.New A T Q))

/-- Rules for destructing encrypted terms -/
inductive Term.Destruct : Process.DesctrKind → Term α β → Term α β → Term α β → Prop where
| SymEnc  : Destruct .SDec (.SEnc M K) K M
  -- Symmetric decryption: `⦃M⦄ˢ K` with key K yields payload M
| AsymEnc : Destruct .ADec (.AEnc M (.Ek K)) K M
  -- Asymmetric decryption: `⦃M⦄ᵃ (Ek K)` with key K yields payload M
| Sign    : Destruct .Ver (.Sign M K) (.Vk K) M
  -- Signature verification: `⟦M⟧ K` with verification key K yields message M

/-- Runtime semantics: Reduction rules for Spi calculus processes.-/
inductive Process.Reduce: Process α β τ -> Process α β τ -> Prop
 | IO     :  Reduce ((Process.Out C M P).Par (Process.In C X T Q)) (P.Par (Q.subst (.Var X) M))
 | Cond1  :  M = N -> Reduce (Process.IfEq M N P Q) P
 | Cond2  :  M ≠ N -> Reduce (Process.IfEq M N P Q) Q
 | Res    : Reduce P Q -> Reduce (.New V T P) (.New V T Q)
 | Par    : Reduce P Q -> Reduce (P.Par R) (Q.Par R)
 | Struct : Reduce P Q -> Equiv P P' -> Equiv Q Q' -> Reduce P' Q'
 | Destr  : Term.Destruct D M K M' -> Reduce (.CaseOf D M X K P) (P.subst (.Var X) M')
