import Mathlib.Tactic
import Leanspi.Pi.Process
import Leanspi.Common.TypingEnvironment
import Leanspi.Common.SecurityLevels


namespace Pi
/-!
# Typing
This files gather all definitions and proofs for typing in the π-calculus.

The main lemmas are `secrecy` and `integrity` at the end of the file
-/

section CoreTypeSystem

/-!
## Types and subtypes
-/

inductive Ty (α: Type) : Type where
  | Level : α -> Ty α
  | Channel : α -> Ty α -> Ty α
  deriving DecidableEq

/-!
We can define a custom notation for channels and an automatic coertion from Security to Ty Security
-/
notation "𝐶'" l:max "⟦" t "⟧" => Ty.Channel l t
instance : Coe (Security) (Ty Security) := ⟨Ty.Level⟩

abbrev Security.LL : Security := ⟨.L, .L⟩
abbrev Security.HH : Security := ⟨.H, .H⟩
abbrev Security.LH : Security := ⟨.L, .H⟩
abbrev Security.HL : Security := ⟨.H, .L⟩
open Security

abbrev Ty.l : Ty α -> α
  | Ty.Level ℓ => ℓ
  | Ty.Channel ℓ _ => ℓ


inductive Ty.Subtype' : Ty Security -> Ty Security -> Prop where
| Channel : Ty.Subtype' (𝐶'ℓ⟦T⟧) ℓ
| CanFlow : ℓ₁ ⊑ ℓ₂ -> Ty.Subtype' ℓ₁ ℓ₂
| LL      : Ty.Subtype' LL (𝐶'LL⟦LL⟧)

abbrev Ty.Subtype := Relation.ReflTransGen Ty.Subtype'
abbrev subtype_refl (T : Ty Security) : T.Subtype T := Relation.ReflTransGen.refl
abbrev subtype_trans (T T' T'' : Ty Security) :  T.Subtype T' -> T'.Subtype T'' -> T.Subtype T'' := Relation.ReflTransGen.trans

lemma level_subtyping {T : Ty Security} : T.Subtype T' -> T.l ⊑ T'.l := by
  intros hs
  have := Relation.ReflTransGen.lift _ level_subtyping' hs
  have := Relation.reflTransGen_eq_self @can_flow_refl @can_flow_trans
  simp_all only
  where
    level_subtyping' (T T' : Ty Security) (hs: T.Subtype' T') : T.l ⊑ T'.l := by
     cases hs <;> try (first| exact can_flow_refl | assumption)


/-!
## Typing Environment and WellFormedness (Γ ⊢ ◆)
-/

variable [DecidableEq α] [DecidableEq β]
abbrev TyEnv α β := TypingEnvironment (Term α β) (Ty Security)


inductive WF : TyEnv α β -> Prop where
| Empty : WF ∅
| Env {M : Term α β} : WF Γ -> Γ[M]? = none -> (∀ ℓ T', T = 𝐶'ℓ⟦T'⟧ -> ℓ = HH) -> WF (Γ ++ (M,T))


/-- Our typing environment is a list, but a WF Γ is a set, so WF Γ implies that any permutation of Γ is WF -/
lemma wf_perm {Γ Γ₁ : TyEnv α β} : List.Perm Γ Γ₁ -> WF Γ₁ -> WF Γ := by
  intro p wf₁
  induction' p with x l₁ l₂ a ih x y l l₁ l₂ l₃ _ _ ih₁ ih
  · simp_all
  · rcases wf₁ with (_|⟨a₃,a₂,a₁⟩)
    apply WF.Env (by simp_all) ?_ (by assumption)
    simp_all[GetElem?.getElem?,TypingEnvironment.get]
    intros a b in₁
    apply a₂
    rw[List.Perm.mem_iff]; apply in₁; tauto
  · rcases wf₁ with (_|⟨wf₂,n₂,a₂⟩)
    rcases wf₂ with (_|⟨wf₃,n₃,a₃⟩)
    have get_elem_cons : ∀ (M M₁ : Term α β) (T : Ty Security) (l: TyEnv α β),
     GetElem?.getElem? (self:= TypingEnvironment.instGetElem?Mem) ((M, T) :: l) M₁ = (l ++ (M, T))[M₁]? :=
     by simp[HAppend.hAppend]
    constructor; constructor
    assumption
    rw[get_elem_cons, TypingEnvironment.get_reduce] at n₂; exact n₂
    rw[<- TypingEnvironment.get_none_mem_not] at n₂
    apply TypingEnvironment.nin_append_ne n₂
    assumption
    rw[get_elem_cons] at n₂ ⊢
    rw[<- TypingEnvironment.get_none_mem_not] at n₂ n₃ ⊢
    have :=  TypingEnvironment.nin_append_ne n₂
    intro c
    rcases TypingEnvironment.in_append_or c with (h|h) <;> exfalso
    exact n₃ h; exact this (Eq.symm h)
    assumption
  · simp_all


lemma wf_not_in {Γ: TyEnv α β} {M : Term α β} {T: Ty Security} (wf: WF (Γ ++ (M,T))) :  M ∉ Γ := by
  cases wf; simp_all[TypingEnvironment.get_none_mem_not]

lemma wf_rec {Γ: TyEnv α β}  {M : Term α β}  {T: Ty Security}  (wf: WF (Γ ++ (M,T))) : WF Γ := by
  cases wf; simp_all

lemma wf_nodup {Γ : TyEnv α β} (wf: WF Γ) : Γ.dom.Nodup := by
  induction' wf with Γ₁ T M a₂ a₁ a ih
  · simp
  · simp_all[TypingEnvironment.dom]
    rw[<- TypingEnvironment.get_none_mem_not] at a₁
    induction' Γ₁ with hd₁ tl₁ ih₁; simp
    have : ∀ (M M₁ : Term α β) (T : Ty Security) (l: TyEnv α β),
     Membership.mem (self:= TypingEnvironment.instMembership) ((M, T) :: l) M₁ = (M₁ ∈ (l ++ (M, T))) :=
     by simp[HAppend.hAppend]
    rw[this] at a₁
    have := TypingEnvironment.nin_append_ne a₁
    have := TypingEnvironment.nin_append_rec a₁
    simp; constructor; assumption
    apply ih₁ (wf_rec a₂) this; simp_all


/-
## Typing Terms (Γ ⊢ M :T)
-/


inductive Term.HasType : TyEnv α β -> Term α β -> Ty Security -> Prop
| Atom : WF Γ -> Γ[M]? = some T -> Term.HasType Γ M T
| Subsumption : Term.HasType Γ M T' -> T'.Subtype T -> Term.HasType Γ M T


/-- As above, if Γ ⊢ M :T, we can type M with type T in all permutations of Γ -/
lemma hasType_perm {Γ: TyEnv α β} {M : Term α β} {T: Ty Security} : List.Perm Γ Γ₁ -> M.HasType Γ₁ T -> M.HasType Γ T := by
  intros p ht
  induction ht with
  | Atom wf sm =>
    have := TypingEnvironment.get_perm_nodup p (wf_nodup (wf_perm p wf)) (M := M)
    apply Term.HasType.Atom (wf_perm p wf)
    simp_all
  | Subsumption _ a ih =>
    apply Term.HasType.Subsumption ih a

lemma termHasType_wf {Γ : TyEnv α β} {M : Term α β} (ht: M.HasType Γ T) : WF Γ := by
  induction ht <;> assumption


lemma high_channels {M : Term α β} {T : Ty Security} : ∀ (Γ : TyEnv α β), M.HasType Γ (𝐶'HH⟦T⟧) -> Γ[M]? = some (𝐶'HH⟦T⟧) := by
  intro Γ ht
  apply Term.HasType.recOn (motive := λ x _ => x = (𝐶'HH⟦T⟧) -> Γ[M]? = some (𝐶'HH⟦T⟧)) ht
  · simp_all only [implies_true]
  · intros T' T _ a₁ a h
    induction' a₁ with T T' hh hh₁ ih; simp_all only [true_implies]
    cases hh₁ <;> try trivial
    simp_all only [reduceCtorEq, false_implies, Ty.Channel.injEq, Security.mk.injEq, and_self, false_and]
  · rfl

lemma high_channels_sub {M : Term α β} {Γ : TyEnv α β} (h: Γ[M]? = some (𝐶'HH⟦T⟧)) (ht: M.HasType Γ T') :  (𝐶'HH⟦T⟧).Subtype T' := by
  induction' ht with _ _ _ T' T₁ _ a a_ih
  · simp_all; constructor
  · apply subtype_trans
    exact a_ih
    exact a

lemma low_channels {M : Term α β} : ∀ (Γ : TyEnv α β), M.HasType Γ (𝐶'LL⟦T⟧) ->  T = LL := by
   intro Γ ht
   apply Term.HasType.recOn (motive := λ x _ => x = (𝐶'LL⟦T⟧) -> T = LL) ht
   · intro T hwf hn heq
     induction hwf
     case Empty => simp_all
     case Env M' a₂ a₁ a ih => cases h: decide (M = M') <;> simp_all[a₁]
                               apply ih; constructor <;> assumption
   · intros T' T _ hsub hl tc
     induction' hsub with b c a' a ih; simp_all only [true_implies]
     cases a <;> try trivial
     simp_all only [Ty.Channel.injEq, true_and]
   · rfl


lemma channel_levels : ∀ (Γ : TyEnv α β) (M: Term α β), M.HasType Γ (𝐶'ℓ⟦T⟧) -> ℓ ∈ [ LL, HH ] := by
  intro Γ M ht
  apply Term.HasType.recOn (motive := λ x _ => x = (𝐶'ℓ⟦T⟧) -> ℓ ∈ [ LL, HH ]) ht
  · intros T' hwf hn hh₁
    induction hwf <;> simp_all
    case Env M' _ _ _ ih => cases h: decide (M=M') <;> simp_all
                            · apply ih; constructor <;> assumption
  · intros T T' _ hsub hl tc
    induction' hsub with b c a' a ih; simp_all only [List.mem_cons, true_implies]
    cases a <;> try trivial
    simp_all only [List.mem_cons,Ty.Channel.injEq, true_or]
  · rfl

lemma uniqueness_channel_types' : ∀ (Γ : TyEnv α β) (N: Term α β),
  N.HasType Γ (𝐶'ℓ⟦T⟧) -> N.HasType Γ (𝐶'ℓ⟦T'⟧) -> T = T' := by
   introv ht ht'
   have hℓ := channel_levels Γ N ht
   simp at hℓ
   cases hℓ
   · simp_all only; simp only [low_channels Γ ht, low_channels Γ ht']
   · simp_all only
     have := high_channels Γ ht
     have := high_channels Γ ht'
     rename_i h _; subst h
     simp_all only [Option.some.injEq, Ty.Channel.injEq, true_and]

lemma uniqueness_channel_types : ∀ (Γ : TyEnv α β) (N: Term α β),
  N.HasType Γ (𝐶'ℓ⟦T⟧) -> N.HasType Γ (𝐶'ℓ'⟦T'⟧) ->  𝐶'ℓ⟦T⟧ = 𝐶'ℓ'⟦T'⟧ := by
   introv ht ht'
   have hℓ  := channel_levels Γ N ht
   have hℓ' := channel_levels Γ N ht'
   cases hℓ <;> cases hℓ'
   · have := uniqueness_channel_types' Γ N ht ht'
     simp_all
   · rename_i a; cases a; rotate_left; rename_i a; cases a
     have := high_channels Γ ht'
     have := high_channels_sub this ht
     have := level_subtyping this
     simp [can_flow, can_flow_integrity, can_flow_confidentiality] at this
   · rename_i a; cases a; rotate_left; rename_i a; cases a
     have := high_channels Γ ht
     have := high_channels_sub this ht'
     have := level_subtyping this
     simp [can_flow, can_flow_integrity, can_flow_confidentiality] at this
   · rename_i a a₁; cases a <;> cases a₁ <;> try (rename_i a; cases a)
     have := uniqueness_channel_types' Γ N ht ht'
     simp_all

/--
For all lemmas about processes, we need the version for terms
-/

lemma hasType_strengthening {Γ : TyEnv α β} {M M' : Term α β} {T T' : Ty Security} :
 M.HasType  (Γ ++ (M', T')) T ->  M' ∉ M.fvfn -> M.HasType Γ T := by
 intros ht nin
 induction ht
 case Atom wf get => constructor; apply wf_rec wf; cases M <;> (simp [Term.fvfn] at nin; rw [<- TypingEnvironment.get_reduce] <;> tauto)
 case Subsumption _ hsub ih => exact Term.HasType.Subsumption ih hsub

lemma hasType_weakening {Γ : TyEnv α β} {M M' : Term α β} {T T' : Ty Security} :
 M.HasType Γ T -> WF (Γ ++ (M', T')) -> M.HasType (Γ ++ (M', T')) T := by
  intros ht wf
  induction ht
  · constructor; assumption
    by_cases M=M'
    · subst M'
      have := wf_not_in wf
      rw [TypingEnvironment.get_none_mem_not] at this; simp_all
    · rw [TypingEnvironment.get_reduce]; assumption; tauto
  · apply Term.HasType.Subsumption <;> assumption

lemma hasType_substitution {Γ : TyEnv α β} {M M' : Term α β} {T T' : Ty Security} :
                           M.HasType (Γ ++ (x, T')) T -> M'.HasType Γ T' -> (M.subst x M').HasType Γ T := by
  intro ht ht'
  induction ht
  · simp; split
    · cases ht'
      · constructor; assumption; simp_all
      · apply Term.HasType.Subsumption (by assumption); simp_all
    · constructor; apply wf_rec (by assumption); simp_all
  · apply Term.HasType.Subsumption <;> assumption


/-!
## Typing Processes (Γ ⊢ P)
-/


inductive Process.WellTyped : Process α β (Ty Security) -> TyEnv α β -> Prop
| Stop  : WF Γ -> Stop.WellTyped Γ
| Par   : P.WellTyped Γ -> Q.WellTyped Γ -> (Par P Q).WellTyped  Γ
| Repl  : P.WellTyped Γ -> (Rep P).WellTyped Γ
| Res   : P.WellTyped (Γ ++ (@Term.Name α β A, T)) -> (New A T P).WellTyped Γ
| Cond  : M.HasType Γ T -> N.HasType Γ T' -> P.WellTyped Γ -> Q.WellTyped Γ -> (IfEq M N P Q).WellTyped Γ
| In    : P.WellTyped (Γ ++ (@Term.Var α β X, T)) -> N.HasType Γ (𝐶' ℓ ⟦T⟧) -> (In N X T P).WellTyped Γ
| Out   : M.HasType Γ T -> P.WellTyped Γ -> N.HasType Γ (𝐶' ℓ ⟦T⟧) -> (Out N M P).WellTyped Γ


lemma processWellTyped_wf  {Γ : TyEnv α β} {P : Process α β (Ty Security)} (ht: P.WellTyped Γ) : WF Γ := by
  induction ht; assumption
  all_goals try simp_all
  all_goals apply wf_rec; assumption

-- As with (Γ ⊢ M :T), we can permute Γ
lemma processWellTyped_perm {Γ: TyEnv α β} {P : Process α β (Ty Security)} :
                            List.Perm Γ Γ₁ -> P.WellTyped Γ₁ -> P.WellTyped Γ := by
  intros p wt
  induction wt generalizing Γ with
  | Stop => apply Process.WellTyped.Stop; apply wf_perm p; assumption
  | Par _ _ ih ih₁ => exact Process.WellTyped.Par (ih p) (ih₁ p)
  | Repl _ ih => exact Process.WellTyped.Repl (ih p)
  | Cond a₁ b₁ _ _ ih ih₁ => apply Process.WellTyped.Cond (hasType_perm p a₁) (hasType_perm p b₁) (ih p) (ih₁ p)
  | Out a₁ _ c₁ ih => apply Process.WellTyped.Out (hasType_perm p a₁) (ih p) (hasType_perm p c₁)
  | Res _ ih => apply Process.WellTyped.Res; apply ih
                simp_all[HAppend.hAppend]
  | In _ a₁ ih => apply Process.WellTyped.In ?_ (hasType_perm p a₁); apply ih
                  simp_all[HAppend.hAppend]


-- In this proof simp is very inefficient: by hardcoding all the rewrite rules and using "simp only" we can make it faster,
-- even if it looks very ugly :/
lemma strengthening {Γ : TyEnv α β} (P: Process α β (Ty Security)) (M : Term α β) (T : Ty Security) :
  P.WellTyped (Γ ++ (M, T)) -> M ∉ P.fvfn -> P.WellTyped Γ := by
  intros wt nin
  induction P generalizing Γ
  case Stop => cases wt; constructor; apply wf_rec (by assumption)
  case In ch var ty P ih =>
    cases wt; constructor
    · have : Term.Var var ≠ M := TypingEnvironment.nin_append_ne $ wf_not_in (processWellTyped_wf (by assumption))
      apply ih (processWellTyped_perm (TypingEnvironment.append_perm) (by assumption))
      simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and,
        and_imp, Process.fv, ne_eq, Term.fv, Process.fn, Term.fn, true_or, not_false_eq_true,
        implies_true, and_true, forall_const]
      grind only
    · apply hasType_strengthening; assumption; simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, ne_eq, Term.fv, Process.fn, Term.fn, Term.fvfn, or_true, not_false_eq_true, implies_true, and_self]
  case New var ty P ih =>
   cases wt; constructor
   · have : Term.Name var ≠ M := TypingEnvironment.nin_append_ne $ wf_not_in (processWellTyped_wf (by assumption))
     apply ih (processWellTyped_perm (TypingEnvironment.append_perm) (by assumption))
     simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and,
        and_imp, Process.fv, ne_eq, Term.fv, Process.fn, Term.fn, true_or, not_false_eq_true,
        implies_true, and_true, forall_const]
     grind only
  case Out =>
    cases wt; constructor
    · apply hasType_strengthening (by assumption); simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, Term.fvfn, or_true, not_false_eq_true, implies_true, and_self]
    · simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, true_or, not_false_eq_true, implies_true]
    · apply hasType_strengthening (by assumption); simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, Term.fvfn, or_true, true_or, not_false_eq_true, implies_true, and_self]
  case Par ih ih1 =>
    cases wt; constructor
    · apply ih (by assumption); simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Process.fn, true_or, not_false_eq_true, implies_true, and_self]
    · apply ih1 (by assumption); simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Process.fn, or_true, not_false_eq_true, implies_true, and_self]
  case Rep ih => cases wt; constructor; simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Process.fn, not_false_eq_true, implies_true]
  case IfEq ih ih1 =>
    cases wt; constructor
    · apply hasType_strengthening (by assumption); simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, Term.fvfn, or_true, true_or, not_false_eq_true, implies_true, and_self]
    · apply hasType_strengthening (by assumption); simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, Term.fvfn, or_true, true_or, not_false_eq_true, implies_true, and_self]
    · simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, true_or, not_false_eq_true, implies_true]
    · simp_all only [Process.fvfn, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, and_imp, Process.fv, Term.fv, Process.fn, Term.fn, or_true, true_or, not_false_eq_true, implies_true]


/-
We have to assume that no shadowing can happen.

This is the case since we did not use a nameless encoding, so shadowing is still possible.

For simplicity, since it is possible to rewrite all proofs with processes where shadowing is impossible
by construction (e.g., using de Burijn indexes), we assume here that we don't have shadowing.
-/
abbrev noCollisions (Γ : TyEnv α β) : Process α β (Ty Security) -> Prop
| .New X _ P => (Term.Name X) ∉ Γ ∧ noCollisions Γ P
| .In _ X _ P => (Term.Var X) ∉ Γ ∧ noCollisions Γ P
| .Rep P => noCollisions Γ P
| .Par P Q => noCollisions Γ P ∧ noCollisions Γ Q
| .IfEq _ _ P Q => noCollisions Γ P ∧ noCollisions Γ Q
| .Out _ _ P => noCollisions Γ P
| .Stop => True

axiom assume_no_shadowing (Γ : TyEnv α β) (P: Process α β (Ty Security)) : noCollisions Γ P

lemma weakening {Γ : TyEnv α β} {M : Term α β} {T : Ty Security} (P: Process α β (Ty Security)) :
 P.WellTyped Γ -> WF (Γ ++ (M, T)) -> P.WellTyped (Γ ++ (M, T)) := by
  intros wt wf
  induction wt
  case Res A T' P Γ a ih =>
    have : M ≠ Term.Name A := by { obtain ⟨nin, _⟩ :=  assume_no_shadowing (Γ ++ (M, T)) (Process.New A T P)
                                   symm; apply TypingEnvironment.nin_append_ne nin }
    constructor
    apply processWellTyped_perm (TypingEnvironment.append_perm)
    apply ih
    have wf₁ := processWellTyped_wf a
    constructor <;> try assumption
    · have := wf_not_in wf
      rw[TypingEnvironment.get_reduce, <- TypingEnvironment.get_none_mem_not] <;> assumption
    · intros ℓ T' a
      have : M ∈ Γ ++ (M,T) := by rw[TypingEnvironment.get_some_mem]; exists T; simp
      cases wf; simp_all
  case In N X T₁ P Γ ℓ a1 a ih =>
    have : M ≠ Term.Var X := by { obtain ⟨nin, _⟩ := assume_no_shadowing (Γ ++ (M, T)) (Process.In N X T P)
                                  symm; apply TypingEnvironment.nin_append_ne nin }
    constructor
    apply processWellTyped_perm (TypingEnvironment.append_perm); apply ih
    have wf₁ := processWellTyped_wf a1
    constructor <;> try assumption
    · have := wf_not_in wf
      rw[TypingEnvironment.get_reduce, <- TypingEnvironment.get_none_mem_not] <;> assumption
    · intros ℓ T' a
      have : M ∈ Γ ++ (M,T) := by rw[TypingEnvironment.get_some_mem]; exists T; simp
      cases wf; simp_all
    · apply hasType_weakening <;> assumption
  all_goals (constructor <;> simp_all)
  all_goals (apply hasType_weakening <;> assumption)


lemma substitution {Γ : TyEnv α β} (P: Process α β (Ty Security)) :
                   P.WellTyped (Γ ++ (x, T)) -> M.HasType Γ T -> (P.subst x M).WellTyped Γ := by
 intro hwf ht
 induction P generalizing Γ
 case Stop => cases hwf; constructor; have := wf_rec (by assumption); tauto
 case Out ih => cases hwf; constructor
                · apply hasType_substitution <;> assumption
                · apply ih <;> assumption
                · apply hasType_substitution <;> assumption
 case Par ih ih1 => cases hwf; constructor <;> simp_all
 case Rep ih => cases hwf; constructor; simp_all
 case IfEq ih ih1 => cases hwf; constructor
                     · apply hasType_substitution <;> assumption
                     · apply hasType_substitution <;> assumption
                     all_goals simp_all
 case New ih => cases hwf
                have wf := processWellTyped_wf (by assumption)
                have := wf_not_in wf
                constructor; apply ih
                · apply processWellTyped_perm (TypingEnvironment.append_perm); assumption
                · apply hasType_weakening ht (wf_rec (wf_perm (TypingEnvironment.append_perm) wf))
 case In ih => cases hwf
               have wf := processWellTyped_wf (by assumption)
               have := wf_not_in wf
               constructor; apply ih
               · apply processWellTyped_perm (TypingEnvironment.append_perm); assumption
               · apply hasType_weakening ht (wf_rec (wf_perm (TypingEnvironment.append_perm) wf))
               · apply hasType_substitution <;> assumption


--------------------------------------------------------------------------------
-- Soundness -- Subject Congruence and Subject Reduction


/-
Given the way WF is defined in the paper,
we have to assume the processes users can write are restricted to only
processes where binders have explicit types that respect the well formedness
of the environment. That is, if the type of a binder is a channel, its level needs to be HH.

With this restriction we are not losing generality as
one can have a LL channel by writing (New x (.Level LL))) instead of (New x (.Channel LL LL)),
and still type it as a channel by Ty.Subtype.
-/
abbrev onlyHHChannelsInBinders : Process α β (Ty Security) -> Prop
| .New _ (.Channel ℓ _) P => ℓ = HH ∧ onlyHHChannelsInBinders P
| .In _ _ (.Channel ℓ _) P => ℓ = HH ∧ onlyHHChannelsInBinders P
| .New _ _ P => onlyHHChannelsInBinders P
| .In _ _ _ P => onlyHHChannelsInBinders P
| .Rep P => onlyHHChannelsInBinders P
| .Par P Q => onlyHHChannelsInBinders P ∧ onlyHHChannelsInBinders Q
| .IfEq _ _ P Q => onlyHHChannelsInBinders P ∧ onlyHHChannelsInBinders Q
| .Out _ _ P => onlyHHChannelsInBinders P
| .Stop => True

axiom type_syntax_restriction : ∀ (P : Process α β (Ty Security)),  onlyHHChannelsInBinders P

-- this lemmas is the (=>) side of the Res0 case of subject congruence
-- we extracted into a definition to highlight where we need to use the above axiom
lemma res0_rhs {Γ : TyEnv α β} (ht :  Process.Stop.WellTyped Γ) : (Process.New A T Process.Stop).WellTyped Γ := by
  cases ht
  have := type_syntax_restriction (Process.New A T Process.Stop) (α := α)
  have := assume_no_shadowing Γ (Process.New A T Process.Stop)
  constructor
  apply weakening
  · constructor; assumption
  · constructor; assumption
    · show Γ[Term.Name A]? = none
      simp_all[TypingEnvironment.get_none_mem_not]
    · show ∀ (ℓ : Security) (T' : Ty Security), T = 𝐶'ℓ⟦T'⟧ → ℓ = HH
      intros; simp_all


lemma subject_congruence_iff {Γ : TyEnv α β} (P Q : Process α β (Ty Security))
                                          (hr : P.Equiv Q ) : P.WellTyped Γ ↔ Q.WellTyped Γ := by
  induction hr generalizing Γ with
  | Refl => simp_all
  | Sym => symm; simp_all only
  | Tran => simp_all only
  | ParR => constructor <;> (intro ht; cases ht; constructor <;> simp_all)
  | Rep => constructor <;> (intro ht; cases ht; constructor; simp_all)
  | Res => constructor <;> (intro ht; cases ht; constructor; simp_all)
  | Res0 => constructor
            · rintro (_|_|_|⟨a⟩); apply strengthening _ _ _ a; simp
            · apply res0_rhs
  | Par0 => constructor
            · intros ht; cases ht; tauto
            · intros ht; constructor; tauto; constructor; apply processWellTyped_wf ht
  | ParS => constructor <;> (intro ht; cases ht; tauto)
  | ParA => constructor
            · intro ht; cases ht; rename_i a a1; cases a; tauto
            · intro ht; cases ht; rename_i a a1; cases a1; tauto
  | ParRep => constructor <;> (intro ht; cases ht; tauto)
  | ResS => constructor <;> (intro ht; cases ht; constructor; rename_i _ a; cases a; constructor
                             apply processWellTyped_perm (TypingEnvironment.append_perm) (by assumption); try tauto)
  | ResF => constructor
            · intro ht; cases ht; rename_i a1 a; cases a; constructor
              · apply strengthening; assumption; simp [*]
              · constructor; assumption
            · intro ht; cases ht; rename_i a1 a; cases a; constructor
              · constructor
                apply weakening; assumption; apply processWellTyped_wf; assumption; assumption


lemma subject_congruence {Γ : TyEnv α β} (P Q : Process α β (Ty Security)) (ht : P.WellTyped Γ) (hr : P.Equiv Q) : Q.WellTyped Γ :=
  (subject_congruence_iff P Q hr).mp ht

lemma subject_reduction {Γ : TyEnv α β} (P Q : Process α β (Ty Security)) (ht : P.WellTyped Γ) (hr : P.Reduce Q) : Q.WellTyped Γ := by
  induction hr generalizing Γ with
  | IO => cases ht; case IO.Par owt iwt =>
     constructor
     · cases owt; assumption
     · apply substitution
       · cases iwt; assumption
       · cases owt; cases iwt
         rename_i _ ht _ _ _ ht' _
         have := uniqueness_channel_types Γ _ ht ht'
         simp_all
  | Cond1 => cases ht; assumption
  | Cond2 => cases ht; assumption
  | Par   => cases ht; tauto
  | Res => cases ht
           case Res.Res a1 a => constructor; apply a1; trivial
  | @Struct P Q P' Q' _ a1 a ih  =>
    have := subject_congruence P' P ht (by constructor; tauto)
    have := subject_congruence Q Q' (ih this)
    tauto


--------------------------------------------------------------------------------
-- Utilities, Permutations of the typing environment


-- The proofs of Secrecy and Integrity require reasoning abut processes with
-- many restrictions in front (scope extrusion): we use manyNew to represent these
-- restrictions as a list
def manyNew (as: List (β × τ)) (p: Process α β τ) :=
  List.foldr (λ (a, T) p => .New a T p) p as

abbrev mkEnv : TyEnv α β -> List (β × Ty Security) -> TyEnv α β :=
  List.foldl (fun g x => g ++ (@Term.Name α β x.1, x.2))

-- many new is well typed by applying many times the new rule
lemma manyNew_well_typed {Γ : TyEnv α β} (h: (manyNew as P).WellTyped Γ) : P.WellTyped (mkEnv Γ as) := by
  rcases as with (_|⟨hd,tl⟩)
  · tauto
  · have : ∀ a T, manyNew ((a,T)::tl) P = .New a T (manyNew tl P)  := by tauto
    rw[this] at h; cases h
    rename_i a
    apply manyNew_well_typed a


-- For the subsequent proofs we need to ignore the mkEnv term created by the above lemma, using it as any other
-- typing environment Γ: to do this, we can prove that
-- mkEnv (Γ ++ (A,B)) ~ (mkEnv Γ) ++ (A,B) where ~ encodes permutation
-- so we can move out of the argument of mkEnv all insertions, adding them to the output of mkEnv
-- This way we can treat any (mkEnv Γ) ++ (A,B) as a Γ' ++ (A,B) where Γ' = (mkEnv Γ)

-- The next section implements the above permutation lemmas.
-- See secrecy and integrity for their usage

lemma List.fold_reverse_append {α} (l l': List α) : List.foldl (λ acc hd => hd::acc) l l' = l'.reverse ++  l := by simp

section perm
variable (Γ Γ' : TyEnv α β) (bs : List (β × Ty Security)) (hd hd': (Term α β × Ty Security))

omit [DecidableEq α] [DecidableEq β] in
/-- Alternative defintion for `mkEnv` using its underlying list backend -/
lemma mkEnv.altDef: -- the terrifying `inferInstance` is to force `++` on lists
  mkEnv Γ bs = (inferInstance: HAppend (List _) (List _) (List _)).hAppend (bs.reverse.map (λ x => (@Term.Name α β x.1, x.2))) Γ := by
    have : mkEnv Γ bs = List.foldl (fun g x => x::g) Γ (bs.map (λ x => (@Term.Name α β x.1, x.2))) := by
      rw[List.foldl_map]; rfl
    rw[this]
    simp_all only [List.foldl_flip_cons_eq_append, List.map_map, List.map_reverse]
    rfl

omit [DecidableEq α] [DecidableEq β] in
/-- `List.perm_middle` for `mkEnv` -/
lemma tyEnv_mkEnv_perm: List.Perm (mkEnv (Γ ++ hd) bs) ((mkEnv Γ bs) ++ hd) := by
  simp_all [mkEnv.altDef]
  apply List.perm_middle

@[simp]
lemma wf_perm_iff (h: List.Perm Γ Γ'): WF Γ ↔ WF Γ' := by
  constructor <;> apply wf_perm
  symm; all_goals assumption

@[simp]
lemma hasType_perm_iff (t: Term α β) (T: Ty Security) (h: List.Perm Γ Γ'): t.HasType Γ T ↔ t.HasType Γ' T := by
  constructor <;> apply hasType_perm
  symm; all_goals assumption

@[simp]
lemma processWellTyped_perm_iff (P : Process α β (Ty Security)) (h: List.Perm Γ Γ'): P.WellTyped Γ ↔ P.WellTyped Γ' := by
  constructor <;> apply processWellTyped_perm
  symm; all_goals assumption
end perm

/-!
## Soundness
-/


theorem secrecy  {Γ : TyEnv α β} (P O P' P'' : Process α β (Ty Security)) :
  (∀ T, (d,T) ∉ bs) -> (∀ T, (b,T) ∉ bs) -> (d ≠ b) ->
  (P.Par O).WellTyped Γ ->
  (P.Par O).Reduce (.New d T (.New b Tb (manyNew bs (P'.Par (.Out (.Name b) (.Name d) P''))))) ->
  T.l.c ⊑c Tb.l.c
  := by
     introv _ _ _ wt this
     replace := subject_reduction _ _ wt this
     rcases this with (_|_|_|⟨this⟩)
     rcases this with (_|_|_|⟨this⟩)
     replace := manyNew_well_typed this
     rcases this with (_|⟨a,this⟩)
     rcases this with (_|_|_|_|_|_|⟨pwt,mt,ct⟩)
     -- Lean needs a bit of help here:
     -- as mentioned above, we want to move all insertions from the input of mkEnv to its ouput
     have hperm: List.Perm (mkEnv (Γ ++ (Term.Name (α:= α) d, T) ++ (Term.Name (α:= α) b, Tb)) bs) ((mkEnv Γ bs) ++ (Term.Name (α:= α) d, T) ++ (Term.Name (α := α) b, Tb)) :=
      by apply List.Perm.trans (by apply tyEnv_mkEnv_perm ); apply List.Perm.cons; apply tyEnv_mkEnv_perm
     -- we can thus use the above hprem rule to rewrite all hypotheses
     simp_all only [ne_eq, not_false_eq_true, implies_true]
     rw[hasType_perm_iff (h:=hperm)] at *
     rw[processWellTyped_perm_iff (h:=hperm)] at *
     clear hperm
     have := channel_levels _ _ ct
     rcases this with (_|⟨_,(_|⟨a⟩)⟩)
     · have := low_channels _ ct
       rcases pwt with (⟨pwf,pget⟩|⟨pht,psub⟩)
       · simp_all; cases (Tb.l.c) <;> simp [can_flow_confidentiality]
       · induction' pht with _ _ _ _ _ _ _ a_ih
         · have := level_subtyping psub
           simp only [can_flow, can_flow_confidentiality, reduceCtorEq, imp_self, implies_true, *] at this
           split at this <;> simp_all [can_flow_confidentiality]
           split <;> try simp
           cases h: (Tb.l.c) <;> tauto
         · apply a_ih; apply subtype_trans <;> assumption
     · have := high_channels _ ct
       cases (T.l.c) <;> simp_all [can_flow_confidentiality]
     · contradiction

theorem integrity {Γ : TyEnv α β} (P O P' P'' : Process α β (Ty Security)) :
  (∀ T, (d,T) ∉ bs) -> (∀ T, (b,T) ∉ bs) -> (d ≠ b) ->
  (P.Par O).WellTyped Γ ->
  (P.Par O).Reduce (.New d T (.New b (𝐶'HH⟦Tb⟧) (manyNew bs (P'.Par (.Out (.Name b) (.Name d) P''))))) ->
  T.l.i ⊑i Tb.l.i
  := by
     introv _ _ _ wt this
     replace := subject_reduction _ _ wt this
     rcases this with (_|_|_|⟨this⟩)
     rcases this with (_|_|_|⟨this⟩)
     replace := manyNew_well_typed this
     rcases this with (_|⟨_,this⟩)
     rcases this with (_|_|_|_|_|_|⟨pwt,mt,ct⟩)
     have hperm: List.Perm (mkEnv (Γ ++ (Term.Name (α:=α) d, T) ++ (Term.Name (α:=α) b, 𝐶'HH⟦Tb⟧)) bs) ((mkEnv Γ bs) ++ (Term.Name (α:=α) d, T) ++ (Term.Name (α:=α) b, 𝐶'HH⟦Tb⟧)) :=
      by apply List.Perm.trans (by apply tyEnv_mkEnv_perm ); apply List.Perm.cons; apply tyEnv_mkEnv_perm
     simp_all only [ne_eq, not_false_eq_true, implies_true]
     rw[hasType_perm_iff (h:=hperm)] at *
     rw[processWellTyped_perm_iff (h:=hperm)] at *
     clear hperm
     rename_i T ℓ a₁ a
     have := channel_levels _ _ ct
     rcases this with (_|⟨_,(_|⟨a⟩)⟩)
     · have := low_channels _ ct
       rcases ct with (⟨cwf,cget⟩|⟨cht,csub⟩)
       · simp_all
       · induction' pwt with T pwf pget T T' pht psub iih
         · rename_i T'; simp_all
           cases h: Tb.l.i  <;> simp_all [can_flow_integrity]
           have ls := level_subtyping csub
           induction cht
           · rename_i T' a a₁; cases h: T'.l.i <;> simp_all [can_flow, can_flow_integrity] <;> subst T' <;> contradiction
           · rename_i T' T'' _ a₁ ih
             have := level_subtyping a₁
             have := can_flow_trans this ls
             cases h: T''.l.i <;> cases h: T'.l.c
              <;> simp_all [can_flow, can_flow_integrity]
             all_goals exact ih (subtype_trans _ _ _ a₁ csub)
         · have a := level_subtyping csub
           rename_i TT _ _ T₁ α T'₁
           cases TT.l.i <;> cases Tb.l.i <;> simp [can_flow_integrity]
           induction' cht with T₃ _ _ T₄ T₅ _ s₁ ih₁
           · simp_all [can_flow, can_flow_integrity, can_flow_confidentiality]; subst T₃; simp_all
           · apply ih₁
             · intros q _
               apply iih q
               cases T₅
               · simp_all [can_flow, can_flow_confidentiality, can_flow_integrity]
               · simp_all [can_flow, can_flow_confidentiality, can_flow_integrity]
             · exact subtype_trans T₄ T₅ 𝐶'LL⟦T'⟧ s₁ csub
             · exact level_subtyping (subtype_trans T₄ T₅ 𝐶'LL⟦T'⟧ s₁ csub)
     · have := high_channels _ ct
       simp_all
       rcases pwt with (⟨pwf,pget⟩|⟨pht,psub⟩)
       · simp_all
         cases T.l.i <;> simp [can_flow_integrity]
       · induction pht
         · simp_all
           rcases (level_subtyping psub) with (⟨_,i⟩)
           assumption
         · rename_i _ a ih
           exact ih (subtype_trans _ _ _ a psub)
     · contradiction
