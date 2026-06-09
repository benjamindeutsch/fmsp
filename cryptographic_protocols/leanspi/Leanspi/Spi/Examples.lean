import Leanspi.Spi.Process
import Leanspi.Common.TypingEnvironment
import Leanspi.Spi.SecrecyIntegrity

namespace Spi

abbrev SProcess := Process String String (Ty Security)
abbrev STerm := Notation.Pi.Term (SProcess)

abbrev Ty.LL : Ty Security := Security.LL
abbrev Ty.LH : Ty Security := Security.LH
abbrev Ty.HH: Ty Security := Security.HH
open KeyKind Security

-- Blanchet authentication protocol

def blanchet.initiator (Tk : Ty Security) (c kA kB : STerm) := pi {
  new k : Tk;
  out(c, ⦃ ⟦ k ⟧ kB ⦄ᵃ (Term.Ek kA) );
  in(c, xe : Ty.LL);
  case xe of ⦃ xm ⦄ˢ k in
  [ success xm ]
}
where success (_ :  Notation.Pi.Term (SProcess)) := Process.Stop

def blanchet.responder (c kA kB : STerm) : SProcess := pi {
  in(c, xe: Ty.LL);
  case xe of ⦃ xs ⦄ᵃ kA in
  case xs of ⟦ xk ⟧ (Term.Vk kB) in
  new m : Ty.HH;
  out(c, ⦃ m ⦄ˢ xk)
}

def blanchet (Ta Tb Tk : Ty Security) : SProcess := pi {
  new c  : Ty.LL;
  new kA : Ta;
  new kB : Tb;
  [ blanchet.initiator Tk c kA kB ] | [ blanchet.responder c kA kB ]
}

macro "wf" : tactic => `(tactic| (repeat (apply WF.Env; constructor)) <;> try ((first| trivial | apply WF.Empty | simp_all); done))


/-- The Blanchet authentication protocol is well-typed. -/
theorem blanchet_wt :
  let Ta := Dec𝐾'HH⟦Ty.HH⟧
  let Tk := Sym𝐾'HH⟦Ty.HH⟧
  let Tb := Sig𝐾'HH⟦Tk⟧
  (blanchet Ta Tb Tk).WellTyped ∅ := by

  simp_all[blanchet]
  apply Process.WellTyped.Res
  apply Process.WellTyped.Res
  apply Process.WellTyped.Res
  apply Process.WellTyped.Par
  · /- initiator -/
    apply Process.WellTyped.Res
    apply Process.WellTyped.Out
    · show (Term.HasType ?Γ ?M LL)
      apply Term.HasType.Subsumption (T':= LH)
      apply Term.HasType.AsymEnc
      · apply Term.HasType.EncKey
        · apply Term.HasType.Atom; wf; aesop
      · apply Term.HasType.DigSig
        · apply Term.HasType.Atom; wf; aesop
        · apply Term.HasType.Atom; wf; aesop
        · simp
      apply Ty.Subtype.single; constructor;  simp [can_flow, can_flow_integrity, can_flow_confidentiality]
    apply Process.WellTyped.In
    apply Process.WellTyped.SymDec
    · apply Term.HasType.Atom; wf; aesop
    · apply Term.HasType.Atom; wf; aesop
    · simp_all[blanchet.initiator.success]
      apply Process.WellTyped.Stop; wf
    · apply Term.HasType.Subsumption
      apply Term.HasType.Atom
      wf; aesop; apply Relation.ReflTransGen.single; constructor
    · apply Term.HasType.Subsumption
      apply Term.HasType.Atom
      wf; aesop; apply Relation.ReflTransGen.single; constructor
  · /- responder -/
    apply Process.WellTyped.In
    · apply Process.WellTyped.AsymDec
      · apply Term.HasType.Atom; wf; aesop
      · apply Term.HasType.Atom; wf; aesop
      apply Process.WellTyped.SignCheck
      · apply Term.HasType.VerKey
        apply Term.HasType.Atom; wf; aesop
      · apply Term.HasType.Atom; wf; aesop
      apply Process.WellTyped.Res
      apply Process.WellTyped.Out
      · show Term.HasType ?Γ ?M LL
        apply Term.HasType.Subsumption
        apply Term.HasType.SymEnc
        apply Term.HasType.Atom; wf; aesop
        apply Term.HasType.Atom; wf; aesop
        apply Relation.ReflTransGen.single; constructor; simp [can_flow, can_flow_integrity, can_flow_confidentiality]
      · apply Process.WellTyped.Stop; wf
      · apply Term.HasType.Subsumption
        apply Term.HasType.Atom; wf; aesop
        apply Relation.ReflTransGen.single; constructor
      · simp
      · /- now we typecheck the process a second time  (see Process.WellTyped.AsymDec) -/
        intros
        apply Process.WellTyped.SignCheck
        · apply Term.HasType.VerKey
          apply Term.HasType.Atom; wf; aesop
        · apply Term.HasType.Atom; wf; aesop
        apply Process.WellTyped.Res
        apply Process.WellTyped.Out
        · show Term.HasType ?Γ ?M LL
          apply Term.HasType.Subsumption
          apply Term.HasType.SymEnc
          apply Term.HasType.Atom; wf; aesop
          apply Term.HasType.Atom; wf; aesop
          apply Relation.ReflTransGen.single; constructor; simp [can_flow, can_flow_integrity, can_flow_confidentiality]
        · apply Process.WellTyped.Stop; wf
        · apply Term.HasType.Subsumption
          apply Term.HasType.Atom; wf; aesop
          apply Relation.ReflTransGen.single; constructor
        simp
    · apply Term.HasType.Subsumption
      apply Term.HasType.Atom; wf; aesop
      apply Relation.ReflTransGen.single; constructor
