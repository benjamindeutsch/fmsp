import Leanspi.Pi.Process
import Leanspi.Common.TypingEnvironment
import Leanspi.Pi.SecrecyIntegrity
import Leanspi.Pi.TypeChecker

namespace Pi

abbrev Proc := Process String String (Ty Security)
abbrev Ty.LL : Ty Security := Security.LL
abbrev Ty.HH : Ty Security := Security.HH
abbrev Ty.LH : Ty Security := Security.LH
abbrev Ty.HL : Ty Security := Security.HL


lemma example_well_typed :
  pi (Proc) {
    new c : Ty.LL;
    new d : 𝐶' Security.HH ⟦ Ty.HL ⟧;
    in(c, x : Ty.LL);
    out(d, x)
  }.WellTyped ∅
:= by
  simp
  apply Process.WellTyped.Res
  apply Process.WellTyped.Res
  apply Process.WellTyped.In
  · apply Process.WellTyped.Out
    · show Term.HasType _ (Term.Var "x") (Ty.HL)
      apply Term.HasType.Subsumption
      · show Term.HasType _ (Term.Var "x") (Ty.LL)
        apply Term.HasType.Atom
        · apply WF.Env
          apply WF.Env
          apply WF.Env
          apply WF.Empty
          all_goals simp
        · show _[Term.Var "x"]? = some Ty.LL
          simp
      · apply Relation.ReflTransGen.single
        apply Ty.Subtype'.CanFlow
        simp [can_flow, can_flow_integrity, can_flow_confidentiality]
    · apply Process.WellTyped.Stop
      · apply_rules [WF.Env, WF.Empty] <;> simp
    · show Term.HasType _ (Term.Name "d") (Ty.Channel Security.HH Ty.HL)
      apply Term.HasType.Atom
      · apply_rules [WF.Env, WF.Empty] <;> simp
      · show _[Term.Name "d"]? = some (Ty.Channel Security.HH Ty.HL)
        simp
  · show Term.HasType _ (Term.Name "c") (Ty.Channel Security.LL Ty.LL)
    apply Term.HasType.Subsumption
    · apply Term.HasType.Atom
      · apply_rules [WF.Env, WF.Empty] <;> simp
      · show _[Term.Name "c"]? = some Ty.LL
        simp
    · apply Relation.ReflTransGen.single
      apply Ty.Subtype'.LL


lemma example_not_well_typed :
  ¬(pi (Proc) {
    new c : Ty.LL;
    new d : 𝐶' Security.HH ⟦ Ty.HL ⟧;
    in(c, x : Ty.HH);
    out(d, x)
  }.WellTyped ∅)
:= by
  simp
  intro wt -- we don't have a lot of choice
  cases wt; case Res wt =>
  cases wt; case Res wt =>
  cases wt; case In ℓ ht wt =>
  /- `ht` is a contradiction. -/
  clear wt -- let's rid ouservelves of the useless hypothesis
  /-
    Doing the proof naively makes us loop on `Subsumption`.
    However, we know that any proof of `ht` is finite. Therefore, we use
    induction on the proof tree that is `ht` !

    However, lean can be dumb we that kind of things. The `induction` tactics cannot
    remove impossible cases, a solution for this is to introduce a variable instead of the
    concrete term. The tactic `generalize` does that for us.
  -/
  generalize hT: 𝐶'ℓ⟦Ty.HH⟧ = T at ht /- This replaces `𝐶'ℓ⟦Ty.HH⟧` by a fresh variable `T` and add the relevant hypothesis -/
  induction ht with
  | Atom _ hin => cases hT;  /- equality only has one constructor -/
                  cases hin
  | Subsumption hrec hsub ih =>
    /- similar but `hsub` already has variables, no need for the `generalize` trick -/
    induction hsub with
    | refl => subst hT; /- purpose built tactic -/ apply ih; rfl
    | tail hrel hsub ih' => subst hT; cases hsub -- impossible


attribute [local simp] can_flow can_flow_confidentiality can_flow_integrity in
lemma example_slide :
  ¬(pi (Proc) {
    new c : Ty.LL;
    new b : 𝐶' Security.HH ⟦ Ty.LH ⟧;
    in(c, x : Ty.LL);
    out(b, x)
  }.WellTyped ∅)
:= by
   simp
   intro wt
   cases wt with | Res wt =>
   cases wt with | Res wt =>
   cases wt with | @In _ _ _ _ _ ℓ wt hc => 
   cases wt with | @Out _ _ _ _ T ℓ ht wt hc =>
   clear wt
   have := uniqueness_channel_types _ _ hc (by 
            apply Term.HasType.Atom
            apply termHasType_wf hc 
            simp[Notation.Pi.mkNam]
            constructor <;> rfl)
   have : T = Ty.LH  := by grind
   clear hc
   induction ht with 
   | Atom a => subst this; simp_all[Notation.Pi.mkVar]
   | @Subsumption T' _ a hs ih => 
     subst this
     by_cases T' = Ty.LH; grind
     have := level_subtyping hs
     cases T' with
     | Level ℓ => cases ℓ with | mk c i => cases c <;> cases i <;> simp_all
     | Channel ℓ => 
       have := channel_levels _ _ a
       cases ℓ with | mk c i => cases c <;> cases i <;> simp_all
   done                                          


lemma exercise_well_typed:
  pi (Proc) {
    new priv : 𝐶' Security.HH ⟦ 𝐶' Security.HH ⟦ Ty.HH ⟧ ⟧;
    !(in(priv, ch : 𝐶' Security.HH ⟦ Ty.HH ⟧);
      new x : Ty.HH;
      out(ch, x))
  }.WellTyped ∅
:= by
  simp
  repeat constructor <;> try simp_all


-------------------------------------------------------------------------------
-- Using the type checker in proofs

-- since we have a Decidable instance we can use the decide tactic to call the type checker

lemma example_well_typed' :
  pi (Proc) {
    new c : Ty.LL;
    new d : 𝐶' Security.HH ⟦ Ty.HL ⟧;
    in(c, x : Ty.LL);
    out(d, x)
  }.WellTyped ∅
:= by decide

lemma example_not_well_typed' :
  ¬(pi (Proc) {
    new c : Ty.LL;
    new d : 𝐶' Security.HH ⟦ Ty.HL ⟧;
    in(c, x : Ty.HH);
    out(d, x)
  }.WellTyped ∅)
:= by decide

lemma exercise_well_typed' :
  pi (Proc) {
    new priv : 𝐶' Security.HH ⟦ 𝐶' Security.HH ⟦ Ty.HH ⟧ ⟧;
    !(in(priv, ch : 𝐶' Security.HH ⟦ Ty.HH ⟧);
      new x : Ty.HH;
      out(ch, x))
  }.WellTyped ∅
:= by decide
