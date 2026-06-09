import Leanspi.Pi.Process
import Leanspi.Common.TypingEnvironment
import Leanspi.Pi.SecrecyIntegrity

namespace Pi

section TypeChecker
variable [DecidableEq α] [DecidableEq β]
open Security

def Term.typeCheck (t: Term α β) (Γ: TyEnv α β) (wf: WF Γ := by assumption) :
    Option { ty: Ty Security // t.HasType Γ ty ∧ (∀ ty', ty.Subtype ty' <-> t.HasType Γ ty' ) } :=
 match h : Γ[t]? with
 | some ty => some ⟨ty, by apply And.intro (HasType.Atom wf h)
                           intro ty'; constructor
                           · intro ht; induction ht
                             · apply HasType.Atom wf h
                             · apply HasType.Subsumption <;> tauto
                           · intro hs; induction hs
                             · simp_all; apply subtype_refl ty
                             · apply subtype_trans ty <;> assumption⟩
 | none => none

theorem term_typecheck_sound {Γ : TyEnv α β} {wf: WF Γ} (m: Term α β)
                             (h: m.typeCheck Γ (wf := wf).isSome) : (∃ T, m.HasType Γ T) := by
  simp [Option.isSome_iff_exists] at h
  obtain ⟨a, ⟨⟨ht,_⟩⟩⟩ := h
  exists a

theorem term_typecheck_sound' {Γ : TyEnv α β} {wf: WF Γ} (m: Term α β) {V}
                             (h: m.typeCheck Γ (wf := wf) = some V) :  m.HasType Γ V.val := by
  exact V.property.left

theorem term_typecheck_complete {Γ : TyEnv α β} {wf: WF Γ} (m: Term α β)
                                (h: m.typeCheck Γ (wf := wf).isNone) : (∀ T, ¬m.HasType Γ T) := by
  intro T
  cases get : Γ[m]?
  case none => intro hs; induction hs <;> simp_all
  case some => simp[Term.typeCheck] at h; split at h <;> simp_all

instance {T T': Ty Security} : Decidable (T.Subtype T') :=
  if hT: T = T' then isTrue (by subst T; constructor) else by
  obtain (ℓ|⟨ℓ, T⟩) := T <;>
  obtain (ℓ'|⟨ℓ', T'⟩) := T'
  case Level.Level =>
    refine if h: ℓ ⊑ ℓ' then isTrue ?_ else isFalse ?_
    · apply Relation.ReflTransGen.single; constructor; assumption
    · intro hs; have := level_subtyping hs; simp_all
  case Level.Channel =>
    refine if h: ℓ ⊑ LL ∧ ℓ' = LL ∧ T' = LL then isTrue ?_ else isFalse ?_
    · apply Relation.ReflTransGen.tail; apply Relation.ReflTransGen.single
      show ((Ty.Level ℓ).Subtype' LL); constructor; simp[*]; simp_all; constructor
    · intro hs; refine hs.recOn (motive := λ x _ => x = _ -> False) ?_ ?_ rfl
      · simp
      · intros; intro hc; simp_all; rename_i a ih; cases a; simp_all
        have := level_subtyping (by assumption)
        simp_all[can_flow, can_flow_confidentiality,can_flow_integrity, Ty.l]
  case Channel.Level =>
    refine if h: ℓ ⊑ ℓ' then isTrue ?_ else isFalse ?_
    · apply Relation.ReflTransGen.tail; apply Relation.ReflTransGen.single
      show (𝐶'ℓ⟦T⟧.Subtype' (Ty.Level ℓ)); constructor; constructor; assumption
    · intros hs; refine hs.recOn (motive := λ x _ => x = _ -> False) ?_ ?_ rfl
      · simp
      · intros b c a₁ a ih hc
        rcases a with (_|⟨a⟩) <;> simp_all <;>
        have := level_subtyping (by assumption) <;>
        simp[Ty.l] at this; simp_all
        have := can_flow_trans this a
        contradiction
  case Channel.Channel =>
    refine if h: ℓ ⊑ LL ∧ ℓ' = LL ∧ T' = LL  then isTrue ?_ else isFalse ?_
    · have cl : 𝐶'ℓ⟦T⟧.Subtype ℓ := by apply Relation.ReflTransGen.single; constructor
      have cl₁ : (Ty.Level ℓ).Subtype (Ty.Level LL) := by apply Relation.ReflTransGen.single; constructor; simp[*]
      have cl₂ : (Ty.Level LL).Subtype 𝐶'LL⟦LL⟧ := by apply Relation.ReflTransGen.single; constructor
      have := subtype_trans _ _ _ (subtype_trans _ _ _ cl cl₁) cl₂
      simp_all only
    · intro hs; refine hs.recOn (motive := λ x _ => x = _ -> False) ?_ ?_ rfl
      · simp_all
      · intro _ _ _ a ih ce
        cases a <;> simp_all
        obtain ⟨ce,ce₁⟩ := ce
        have := level_subtyping hs
        simp_all


attribute [local simp] TypingEnvironment.get_none_mem_not

def Process.typeCheck (p: Process α β (Ty Security)) (Γ: TyEnv α β) (wf : WF Γ := by assumption) : Option { _u: Unit // p.WellTyped Γ } := do
  let _ := assume_no_shadowing Γ p
  let _ := type_syntax_restriction p

  match h: p with
  | Stop => pure ⟨(), by tauto⟩
  | Rep q => do
     let ⟨_, qt⟩ <- q.typeCheck Γ
     pure (by tauto)
  | Par q r => do
     let ⟨_, qt⟩ <- q.typeCheck Γ
     let ⟨_, rt⟩ <- r.typeCheck Γ
     pure (by tauto)
  | New m t p => do
     let newΓ := (Γ ++ (@Term.Name α β m, t))
     have newΓwf : WF newΓ := WF.Env wf (by aesop) (by aesop)
     let ⟨_, qt⟩ <- p.typeCheck newΓ
     pure (by tauto)
  | IfEq m n q r => do
     let ⟨mt, mh⟩ <- m.typeCheck Γ
     let ⟨nt, nh⟩ <- n.typeCheck Γ
     let ⟨_, qt⟩ <- q.typeCheck Γ
     let ⟨_, rt⟩ <- r.typeCheck Γ
     pure ⟨(), by cases mh; cases nh; constructor <;> assumption⟩
  | Out c m q => do
     let ⟨mt, ms⟩ <- m.typeCheck Γ
     let ⟨ct, ch⟩ <- c.typeCheck Γ
     let ⟨_, qt⟩ <- q.typeCheck Γ
     match ct with
     | .Level ℓ =>
         if hℓ: ℓ ⊑ LL ∧ mt.Subtype LL
         then pure ⟨(), by
               apply Process.WellTyped.Out ((ms.right LL).mp (by tauto)) qt
               apply Term.HasType.Subsumption (ch.left)
               apply subtype_trans _ _ _ (Relation.ReflTransGen.single (Ty.Subtype'.CanFlow hℓ.left))
               apply Relation.ReflTransGen.single; simp_all; constructor⟩
         else none
     | .Channel ℓ T =>
         if ht: mt.Subtype T
         then pure ⟨(), Process.WellTyped.Out ((ms.right T).mp ht) qt ch.left⟩
         else none
  | In c x t q => do
     let newΓ := (Γ ++ (@Term.Var α β x, t))
     have newΓwf : WF newΓ := WF.Env wf (by aesop) (by aesop)
     let ⟨_, qt⟩ <- q.typeCheck newΓ
     let ⟨ct, ch⟩ <- c.typeCheck Γ
     match ct with
     | .Level ℓ =>
         if hℓ: ℓ ⊑ LL ∧ t = LL
         then pure ⟨(), by
           refine Process.WellTyped.In qt ((ch.right (𝐶'LL⟦t⟧)).mp ?_);
           apply subtype_trans _ _ _ (Relation.ReflTransGen.single (Ty.Subtype'.CanFlow hℓ.left))
           apply Relation.ReflTransGen.single; simp_all; constructor ⟩
         else none
     | .Channel ℓ T =>
         if ht: t = T
         then pure ⟨(), by apply Process.WellTyped.In qt ((ch.right (𝐶'ℓ⟦t⟧)).mp (by simp_all))⟩
         else none



theorem typecheck_sound {Γ : TyEnv α β} {wf: WF Γ} (p: Process α β (Ty Security))
                                                   (h: p.typeCheck Γ (wf := wf).isSome) : p.WellTyped Γ := by
  obtain ⟨⟨_, h⟩⟩ := Option.isSome_iff_exists.mp h
  exact h


lemma channel_subtypes_low (h: (Ty.Level a).Subtype (𝐶'ℓ⟦T⟧)) : a ⊑ LL ∧ ℓ = LL ∧ T = LL := by
  refine h.rec (motive := fun x _ => x = _ -> _) ?_ ?_ rfl
  · simp_all
  · intros b c a₁ a ih ce
    cases a <;> simp_all
    have := level_subtyping a₁
    obtain ⟨left, right⟩ := ce
    simp_all


theorem typecheck_complete {Γ : TyEnv α β} {wf: WF Γ} (p: Process α β (Ty Security))
                                                      (h: p.typeCheck Γ (wf := wf).isNone) : ¬p.WellTyped Γ := by
  induction p generalizing Γ
  case Stop => simp[Process.typeCheck] at h
  case Par a a₁ ih ih₁ =>
    cases ha: a.typeCheck Γ (wf:=wf) <;> cases ha₁: a₁.typeCheck Γ (wf:=wf) <;>
    (intro ht; cases ht; simp_all[Process.typeCheck])
  case Rep a ih =>
    cases ha: a.typeCheck Γ (wf:=wf) <;>
    (intro ht; cases ht; simp_all[Process.typeCheck])
  case New n t p ih =>
    intro ht; cases ht; simp_all[Process.typeCheck]
    rename_i a
    cases ha: p.typeCheck (Γ ++ (@Term.Name α β n, t)) (wf := processWellTyped_wf a)
    · specialize ih ha; contradiction
    · simp_all
  case IfEq a b thn els iht ihe =>
    cases ha: thn.typeCheck Γ (wf:=wf) <;> cases ha₁: els.typeCheck Γ (wf:=wf) <;>
    (intro ht; cases ht; simp_all only [Process.typeCheck, Option.isNone_iff_eq_none, Option.pure_def, Option.bind_eq_bind,
                                        Option.bind_none, Option.bind_eq_none_iff, Subtype.forall])
    cases ht: a.typeCheck Γ <;> cases ht₁: b.typeCheck Γ (wf := wf)
    · rename_i a₃ a₂ _ _;   apply term_typecheck_complete _ (by simp only [Option.isNone_iff_eq_none,ht]) _ a₃ (wf := wf)
    · rename_i a₃ a₂ _ _ _; apply term_typecheck_complete _ (by simp only [Option.isNone_iff_eq_none,ht]) _ a₃ (wf := wf)
    · rename_i a₃ a₂ _ _ _; apply term_typecheck_complete _ (by simp only [Option.isNone_iff_eq_none,ht₁]) _ a₂ (wf := wf)
    · rename_i a₃ a₂ _ _ v₁ v₂;
      obtain ⟨t₁, ⟨ht₁,hp₁⟩⟩ := v₁
      obtain ⟨t₂, ⟨ht₂,hp₂⟩⟩ := v₂
      simp only [Option.some.injEq, Subtype.mk.injEq, reduceCtorEq, imp_false, not_true_eq_false,
        forall_const, and_imp, *] at h
      apply h <;> trivial

  case Out c m a ih =>
    cases ha: a.typeCheck Γ (wf:=wf) <;> cases hc: c.typeCheck Γ (wf:=wf) <;> cases hm: m.typeCheck Γ (wf:=wf)
    <;> (intro ht; cases ht; simp_all only [Process.typeCheck, Option.isNone_iff_eq_none, Option.pure_def, Option.bind_eq_bind,
                                            Option.bind_none, Option.bind_eq_none_iff, Subtype.forall])
    · rename_i a₂ _ _; apply term_typecheck_complete c (by simp only [Option.isNone_iff_eq_none,hc]) _ a₂ (wf := wf)
    · rename_i a₂ _ _; apply term_typecheck_complete c (by simp only [Option.isNone_iff_eq_none,hc]) _ a₂ (wf := wf)
    · rename_i _ a₁ _; apply term_typecheck_complete m (by simp only [Option.isNone_iff_eq_none,hm]) _ a₁ (wf := wf)
    · rename_i v₁ v₂ _ _ _ a₂ a₁ _;
      obtain ⟨t₁, ⟨ht₁,hp₁⟩⟩ := v₁
      obtain ⟨t₂, ⟨ht₂,hp₂⟩⟩ := v₂
      specialize h t₂ _ rfl t₁ _ rfl () (True.intro) (True.intro)
      simp_all
      cases t₁
      · rename_i T ℓ _ a
        have := (hp₂ T).mpr a₁
        have := (hp₁ 𝐶'ℓ⟦T⟧).mpr a₂
        have := channel_subtypes_low this
        simp_all
      · have := uniqueness_channel_types _  _ a₂ ht₁
        simp_all
  case In c x t p ih =>
    intro ht; cases ht; rename_i ℓ a₁ a
    have wfNew :=  processWellTyped_wf a
    cases ha: p.typeCheck (Γ ++ (@Term.Var α β x, t)) (wf := wfNew) <;> cases hc: c.typeCheck Γ (wf:=wf)
    <;>  (simp_all [Process.typeCheck])
    · apply term_typecheck_complete c (by simp only [Option.isNone_iff_eq_none, hc]) _ a₁ (wf := wf)
    · rename_i v₁
      obtain ⟨t₁, ⟨ht₁,hp₁⟩⟩ := v₁
      simp_all
      cases t₁ <;> simp_all
      · rename_i α
        have := (hp₁ 𝐶'ℓ⟦t⟧).mpr a₁
        have := channel_subtypes_low this
        simp_all
      · have := uniqueness_channel_types _  _ a₁ ht₁
        simp_all

-- Decidability of type checking

instance Process.instDecidableTypeCheck {Γ : TyEnv α β} {wf: WF Γ} (P : Process α β (Ty Security)) :
  Decidable (P.WellTyped Γ) :=
    match h: P.typeCheck Γ (wf := wf) with
    | some ⟨(), pr⟩ => isTrue pr
    | none => isFalse (typecheck_complete P (Option.isNone_iff_eq_none.mpr h) (wf := wf))

instance Process.instDecidableTypeCheckEmpty (P : Process α β (Ty Security)) :
  Decidable (P.WellTyped ∅) := Process.instDecidableTypeCheck (Γ := ∅) (wf := WF.Empty) P


-------------------------------------------------------------------------------
section CheckCollisions

-- Here we show an example on how to implement the checkers to validate our
-- assumptions (axioms) about collisions in Γ and the restrictions on the sytnax of types.
-- We could have used these in the definition of Process.typeCheck,
-- But the completeness proof would have been slighlty more complicated.
-- We can, anyway, call the functions before the typechecker in executable code
-- to make sure our assumptions are valid.

instance {Γ : TyEnv α β} : Decidable (M ∈ Γ) := by
  simp_all[Membership.mem]
  cases TypingEnvironment.get Γ M
  · apply isFalse; simp
  · apply isTrue; simp

def Process.checkCollisions (Γ: TyEnv α β) (p: Process α β (Ty Security)) : Option { _u:Unit // noCollisions Γ p } :=
  match p with
  | Stop => some ⟨(), by simp[noCollisions]⟩
  | Rep q => q.checkCollisions Γ >>= λ x => some (by aesop)
  | Par p q => do
    let c <- p.checkCollisions Γ
    let d <- q.checkCollisions Γ
    some (by aesop)
  | IfEq m n p q => do
    let c <- p.checkCollisions Γ
    let d <- q.checkCollisions Γ
    some (by aesop)
  | Out c m p => do
    let _ <- p.checkCollisions Γ
    some (by aesop)
  | New m t p => do
    let c <- p.checkCollisions Γ
    if h: (@Term.Name α β m) ∈ Γ then none
    else some (by aesop)
  | In c x m p => do
    let _ <- p.checkCollisions Γ
    if h: (@Term.Var α β x) ∈ Γ then none
    else some (by aesop)

lemma checkCollision_complete (Γ: TyEnv α β) (p: Process α β (Ty Security)) : (p.checkCollisions Γ).isNone -> ¬ (noCollisions Γ p) := by
  intro nc
  induction p <;> simp_all only [Option.isNone_iff_eq_none, Process.checkCollisions, Option.bind_eq_bind,
                                 not_and, eq_mpr_eq_cast, Option.bind_eq_bind, Option.isNone_some, Bool.false_eq_true]
  case In a ih => intro nin e; cases h: (Process.checkCollisions Γ a) <;> simp_all
  case New a ih => intro nin e; cases h: (Process.checkCollisions Γ a) <;> simp_all
  case Out a ih => intro e; cases h: (Process.checkCollisions Γ a) <;> simp_all
  case Rep a ih => intro e; cases h: (Process.checkCollisions Γ a) <;> simp_all
  case Par a₁ a₂ ih ih' => intro e e'; cases h: (Process.checkCollisions Γ a₁) <;> cases h₂: (Process.checkCollisions Γ a₂) <;> simp_all
  case IfEq a₁ a₂ ih ih' => intro e e'; cases h: (Process.checkCollisions Γ a₁) <;> cases h₂: (Process.checkCollisions Γ a₂) <;> simp_all


attribute [local simp] onlyHHChannelsInBinders

omit [DecidableEq α] [DecidableEq β] in
def Process.checkSyntax (p: Process α β (Ty Security)) : Option {_u :Unit // onlyHHChannelsInBinders p } :=
  match p with
  | Stop => some ⟨(), by aesop⟩
  | Rep q => q.checkSyntax >>= λ x => some (by aesop)
  | Par p q => do
    let c <- p.checkSyntax
    let d <- q.checkSyntax
    some (by aesop)
  | IfEq m n p q => do
    let c <- p.checkSyntax
    let d <- q.checkSyntax
    some (by aesop)
  | Out c m p => do
    let _ <- p.checkSyntax
    some (by aesop)
  | New m t p => do
    let c <- p.checkSyntax
    match t with
    | (.Channel ℓ _) => if h: ℓ = HH then some (by aesop) else none
    | (.Level ℓ) => some (by aesop)
  | In c x t p => do
    let _ <- p.checkSyntax
    match t with
    | (.Channel ℓ _) => if h: ℓ = HH then some (by aesop) else none
    | (.Level ℓ) => some (by aesop)

omit [DecidableEq α] [DecidableEq β] in
lemma checkSyntax_complete (p: Process α β (Ty Security)) : (p.checkSyntax).isNone -> ¬ (onlyHHChannelsInBinders p) := by
  intro nc
  induction p <;> simp_all only [Option.isNone_some, Bool.false_eq_true, cast_cast, Option.isNone_iff_eq_none, onlyHHChannelsInBinders,
                                 Process.checkSyntax, eq_mpr_eq_cast, id_eq, Option.bind_eq_bind, not_and]
  case Out a ih => intro e; cases h: (Process.checkSyntax a) <;> simp_all
  case In a ih => intro e; cases h: (Process.checkSyntax a) <;> simp_all only [true_implies] <;>
                  (unfold onlyHHChannelsInBinders at e; split at e <;> aesop)
  case New a ih => intro e; cases h: (Process.checkSyntax a) <;> simp_all only [true_implies] <;>
                  (unfold onlyHHChannelsInBinders at e; split at e <;> aesop)
  case Par a₁ a₂ ih₁ ih₂ => intro e; cases h₁: (Process.checkSyntax a₁) <;> cases h₂: (Process.checkSyntax a₂) <;> simp_all
  case Rep a ih => intro e; cases h: (Process.checkSyntax a) <;> simp_all
  case IfEq a₁ a₂ ih₁ ih₂ => intro e; cases h₁: (Process.checkSyntax a₁) <;> cases h₂: (Process.checkSyntax a₂) <;> simp_all

end CheckCollisions


end TypeChecker
