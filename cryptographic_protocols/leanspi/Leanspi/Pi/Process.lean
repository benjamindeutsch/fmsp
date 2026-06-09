import Mathlib.Data.Set.Basic
import Leanspi.Notation


namespace Pi
  inductive Term (α β: Type): Type where
    | Var : α → Term α β
    | Name : β → Term α β
  deriving Repr, DecidableEq

  inductive Process (α β τ : Type) : Type where
    | Stop
    | In (channel: Term α β) (var: α) (type: τ) : Process α β τ → Process α β τ
    | Out (channel: Term α β) (msg: Term α β) : Process α β τ → Process α β τ
    | New (name: β) (type: τ) : Process α β τ → Process α β τ
    | Par : Process α β τ → Process α β τ → Process α β τ
    | Rep : Process α β τ → Process α β τ
    | IfEq (a: Term α β ) (b: Term α β ) (thn: Process α β τ) (els: Process α β τ) : Process α β τ
  deriving Repr, DecidableEq

  @[simp]
  instance {α β τ} : Notation.Pi (Process α β τ) where
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

  variable {α β τ} [DecidableEq α] [DecidableEq β]


  @[simp]
  def Term.subst (T: Term α β) (x: Term α β) (M: Term α β) : Term α β := if T = x then M else T

  @[simp]
  def Process.subst (P: Process α β τ) (x: Term α β) (M: Term α β) : Process α β τ :=
    match P with
    | In c v t P   => In (c.subst x M) v t (P.subst x M)
    | Out c m P    => Out (c.subst x M) (m.subst x M) (P.subst x M)
    | New v t P    => New v t (P.subst x M)
    | Par P Q      => Par (P.subst x M) (Q.subst x M)
    | Rep P        => Rep (P.subst x M)
    | IfEq a b P Q => IfEq (a.subst x M) (b.subst x M) (P.subst x M) (Q.subst x M)
    | Stop         => Stop

  @[simp] def Term.fv : Term α β → Set α
    | Var a  => { a } | _ => ∅
  @[simp] def Term.fn : Term α β → Set β
    | Name a => { a } | _ => ∅
  @[simp] def Term.fvfn (t: Term α β) := { Term.Var v | v ∈ t.fv } ∪ { Term.Name n | n ∈ t.fn }


  @[simp]
  def Process.fv : Process α β τ → Set α
    | In c v _ P   => { x | x ∈ P.fv ∧ x ≠ v } ∪ c.fv
    | Out c m P    => P.fv ∪ c.fv ∪ m.fv
    | New _ _ P    => P.fv
    | Par P Q      => P.fv ∪ Q.fv
    | Rep P        => P.fv
    | IfEq a b P Q => P.fv ∪ Q.fv ∪ a.fv ∪ b.fv
    | Stop         => ∅
  @[simp]
  def Process.fn : Process α β τ → Set β
    | In c _ _ P   => P.fn ∪ c.fn
    | Out c m P    => P.fn ∪ c.fn ∪ m.fn
    | New v _ P    => { x | x ∈ P.fn ∧ x ≠ v }
    | Par P Q      => P.fn ∪ Q.fn
    | Rep P        => P.fn
    | IfEq a b P Q => P.fn ∪ Q.fn ∪ a.fn ∪ b.fn
    | Stop         => ∅
  @[simp]
  def Process.fvfn (t: Process α β τ) := { Term.Var v | v ∈ t.fv } ∪ { Term.Name n | n ∈ t.fn }


  inductive Process.Equiv : Process α β τ → Process α β τ → Prop where
  | Refl {P}          : Equiv P P
  | Sym {P Q}         : Equiv P Q → Equiv Q P
  | Tran {P Q R}      : Equiv P Q → Equiv Q R → Equiv P R
  | ParR {P Q R}      : Equiv P Q → Equiv (P.Par R) (Q.Par R)
  | Rep {P Q}         : Equiv P Q → Equiv (P.Rep) (Q.Rep)
  | Res {P Q A T}     : Equiv P Q → Equiv (.New A T P) (.New A T Q)
  | Res0 {A T}        : Equiv (.New A T (.Stop)) (.Stop)
  | Par0 {P}          : Equiv (P.Par .Stop) P
  | ParS {P Q}        : Equiv (.Par P Q) (.Par Q P)
  | ParA {P Q R}      : Equiv ((Process.Par P Q).Par R) (P.Par (Q.Par R))
  | ParRep {P}        : Equiv (P.Rep) (Process.Par P (P.Rep))
  | ResS {A B T T' P} : A ≠ B → Equiv (.New A T (.New B T' P)) (.New B T' (.New A T P))
  | ResF {A T P Q}    : A ∉ P.fn → Equiv (.New A T (Process.Par P Q)) (P.Par (.New A T Q))

  inductive Process.Reduce : Process α β τ → Process α β τ → Prop where
  | IO {C M P X T Q}    : Reduce ((Process.Out C M P).Par (Process.In C X T Q)) (P.Par (Q.subst (.Var X) M))
  | Cond1 {M N P Q}     : M = N → Reduce (Process.IfEq M N P Q) P
  | Cond2 {M N P Q}     : M ≠ N → Reduce (Process.IfEq M N P Q) Q
  | Res {P Q V T}       : Reduce P Q → Reduce (.New V T P) (.New V T Q)
  | Par {P Q R}         : Reduce P Q → Reduce (P.Par R) (Q.Par R)
  | Struct {P Q P' Q'}  : Reduce P Q → Equiv P P' → Equiv Q Q' → Reduce P' Q'
