import Mathlib.Tactic
import Mathlib.Logic.Relation
import Leanspi.Spi.Process
import Leanspi.Common.TypingEnvironment
import Leanspi.Common.SecurityLevels

namespace Spi

/-- *NB* This is an homemade tactic !
An `apply` that tries to close any remaning goal with `assumption` -/
syntax "aapply" term ("at" ident)?  : tactic -- extend lean's syntax
macro_rules -- defines what the new syntax does
  |`(tactic| aapply $l:term) => `(tactic| apply $l <;> try assumption)
  /- so `aapply h` get replaced by `apply h <;> try assumption`.
     In other words, it calls `apply` then tries `assumption` on all newly generated goals -/
  |`(tactic| aapply $l:term at $h:ident) => `(tactic| apply $l at $h <;> try assumption)
  -- the `at` variant


/-!
## Types and subtypes
The main type here is `Ty`
-/

/--
Spi has types for keys that encode what a key is supposed to do. This is captured by `KeyKind`
-/
inductive KeyKind : Type where
  -- symmectric encryption key
  | Sym
  -- asymmertric encryption private/public keys
  | Enc | Dec
  -- signing/verifying keys
  | Sig | Ver
deriving Repr, DecidableEq, Inhabited
open KeyKind

namespace KeyKind
  /-- is it a secret key? -/
  inductive isSec: KeyKind → Prop
  | Sym: isSec Sym
  | Dec: isSec Dec
  | Sig: isSec Sig

  /-- is it a public key?  -/
  inductive isPub: KeyKind → Prop
  | Enc: isPub Enc
  | Vec: isPub Ver

  -- adds the `isSec`/`isPub` constuctors as lemmas to `simp`
  attribute [simp] isSec.Sym
  attribute [simp] isSec.Dec
  attribute [simp] isSec.Sig
  attribute [simp] isPub.Enc
  attribute [simp] isPub.Vec
end KeyKind


inductive Ty (α: Type) : Type where
| Level : α -> Ty α
| Channel : α -> Ty α -> Ty α
| Key : KeyKind -> α -> Ty α -> Ty α
deriving DecidableEq

/-! ### Fancy notations -/

notation "𝐶'" l:max "⟦" t "⟧" => Ty.Channel l t
notation k "𝐾'" l:max "⟦" t "⟧" => Ty.Key k l t
instance : Coe (Security) (Ty Security) := ⟨Ty.Level⟩

abbrev Security.LL : Security := ⟨.L, .L⟩
abbrev Security.HH : Security := ⟨.H, .H⟩
abbrev Security.LH : Security := ⟨.L, .H⟩
abbrev Security.HL : Security := ⟨.H, .L⟩
open Security

/-! ### The `Ty` type and subdefinitions-/

abbrev Ty.l : Ty α -> α
  | Ty.Level ℓ => ℓ
  | Ty.Channel ℓ _ => ℓ
  | Ty.Key _ ℓ _ => ℓ


inductive Ty.Subtype' : Ty Security -> Ty Security -> Prop where
| Channel {ℓ T}   : Ty.Subtype' (𝐶'ℓ⟦T⟧) ℓ
| Key {μ ℓ T}     : Ty.Subtype' (μ𝐾'ℓ⟦T⟧) ℓ
| CanFlow {ℓ₁ ℓ₂} : ℓ₁ ⊑ ℓ₂ -> Ty.Subtype' ℓ₁ ℓ₂
| LLC             : Ty.Subtype' LL (𝐶'LL⟦LL⟧)
| LLK {μ}         : Ty.Subtype' LL (μ𝐾'LL⟦LL⟧)

abbrev Ty.Subtype := Relation.ReflTransGen Ty.Subtype'
abbrev subtype_refl (T : Ty Security) : T.Subtype T := Relation.ReflTransGen.refl
abbrev subtype_trans (T T' T'' : Ty Security) :  T.Subtype T' -> T'.Subtype T'' -> T.Subtype T'' := Relation.ReflTransGen.trans

/-!
## Typing of term and processes
-/

variable {α β } [DecidableEq α] [DecidableEq β]
abbrev TyEnv α β := TypingEnvironment (Term α β) (Ty Security)

/-! ### Terms -/

inductive Term.isNameOrVar: Term α β → Prop
| Var: Term.isNameOrVar (.Var x)
| Name: Term.isNameOrVar (.Name x)

example {M:Term α β}: M.isNameOrVar ↔ (∃ x, M = .Var x) ∨ (∃ n, M = .Name n) := by
  aesop (add safe constructors Term.isNameOrVar, safe cases Term.isNameOrVar) -- <- by magic to keep the proof in one line

inductive WF : TyEnv α β -> Prop where
| Empty : WF ∅
| Env {M : Term α β} : M.isNameOrVar → WF Γ -> Γ[M]? = none -> (∀ ℓ T', T = 𝐶'ℓ⟦T'⟧ -> ℓ = HH) -> (∀ μ ℓ T', T = μ𝐾'ℓ⟦T'⟧ -> ℓ = HH ∧ μ ∈ [KeyKind.Sym, KeyKind.Dec, KeyKind.Sig]) -> WF (Γ ++ (M,T))


inductive Term.HasType : TyEnv α β -> Term α β -> Ty Security -> Prop
| Atom : WF Γ -> Γ[M]? = some T -> Term.HasType Γ M T
| Subsumption : Term.HasType Γ M T' -> T'.Subtype T -> Term.HasType Γ M T
| EncKey : K.HasType Γ (Dec𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> (Ek K).HasType Γ (Enc𝐾'⟨.L, ℓi⟩⟦T⟧)
| VerKey : K.HasType Γ (Sig𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> (Vk K).HasType Γ (Ver𝐾'⟨.L, ℓi⟩⟦T⟧)
| SymEnc {M K: Term α β} :
         K.HasType Γ (Sym𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> M.HasType Γ T ->
         (M.SEnc K).HasType Γ (Ty.Level ⟨.L, ℓi⟩)
| AsymEnc {M K: Term α β} :
          K.HasType Γ (Enc𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> M.HasType Γ T ->
          (M.AEnc K).HasType Γ (Ty.Level ⟨.L, ℓi⟩)
| DigSig {M K: Term α β} :
         K.HasType Γ (Sig𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> M.HasType Γ T ->
         T.l.c = ℓc ->
         (M.Sign K).HasType Γ (Ty.Level ⟨ℓc, ℓi⟩)

/-! ### Processes -/

inductive Process.WellTyped : Process α β (Ty Security) -> TyEnv α β -> Prop
| Stop  : WF Γ -> Stop.WellTyped Γ
| Par   : P.WellTyped Γ -> Q.WellTyped Γ -> (Par P Q).WellTyped  Γ
| Repl  : P.WellTyped Γ -> (Rep P).WellTyped Γ
| Res   : P.WellTyped (Γ ++ (@Term.Name α β A, T)) -> (New A T P).WellTyped Γ
| Cond  : M.HasType Γ T -> N.HasType Γ T' ->
          P.WellTyped Γ -> Q.WellTyped Γ -> (IfEq M N P Q).WellTyped Γ
| In    : P.WellTyped (Γ ++ (@Term.Var α β X, T)) -> N.HasType Γ (𝐶' ℓ ⟦T⟧) ->
          (In N X T P).WellTyped Γ
| Out   : M.HasType Γ T -> P.WellTyped Γ -> N.HasType Γ (𝐶' ℓ ⟦T⟧) ->
          (Out N M P).WellTyped Γ
| SymDec {M K: Term α β} :
         K.HasType Γ (Sym𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> M.HasType Γ T' ->
         P.WellTyped (Γ ++ (@Term.Var α β X, T)) ->
         (CaseOf .SDec M X K P).WellTyped Γ
| AsymDec {M K: Term α β} :
         K.HasType Γ (Dec𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> M.HasType Γ T' ->
         P.WellTyped (Γ ++ (@Term.Var α β X, T)) ->
         (T'.l.i = .L -> P.WellTyped (Γ ++ (@Term.Var α β X, Ty.Level LL))) ->
         (CaseOf .ADec M X K P).WellTyped Γ
| SignCheck {M K: Term α β} :
         K.HasType Γ (Ver𝐾'⟨ℓc, ℓi⟩⟦T⟧) -> M.HasType Γ T' ->
         P.WellTyped (Γ ++ (@Term.Var α β X, T)) ->
         (T'.l.c = .H -> ℓi = .H) ->
         (CaseOf .Ver M X K P).WellTyped Γ
| NonceCheck {M: Term α β} {n: β} : -- n is nonce
         M.HasType Γ T -> Γ[Term.Name (α:=α) n]? = some T' -> ¬(T'.l ⊑ T.l) -> Q.WellTyped Γ ->
         (IfEq M (Term.Name (α:=α) n) P Q).WellTyped Γ

/-!
### Supporting lemmas
Here we assume some properties as we proved them for Pi
-/

/-! #### channel properties -/
axiom high_channels {M : Term α β} {T : Ty Security} : ∀ (Γ : TyEnv α β), M.HasType Γ (𝐶'HH⟦T⟧) -> Γ[M]? = some (𝐶'HH⟦T⟧)
axiom low_channels {M : Term α β} {T : Ty Security} : ∀ (Γ : TyEnv α β), M.HasType Γ (𝐶'LL⟦T⟧) ->  T = LL
axiom channel_levels {ℓ : Security} {T : Ty Security} : ∀ (Γ : TyEnv α β) (M: Term α β), M.HasType Γ (𝐶'ℓ⟦T⟧) -> ℓ ∈ [ LL, HH ]

axiom uniqueness_channel_types {ℓ ℓ' : Security} {T T' : Ty Security} :
  ∀ (Γ : TyEnv α β) (N: Term α β),
  N.HasType Γ (𝐶'ℓ⟦T⟧) -> N.HasType Γ (𝐶'ℓ'⟦T'⟧) ->  𝐶'ℓ⟦T⟧ = 𝐶'ℓ'⟦T'⟧


/-! #####  strengthening/weakening/substitution -/

axiom hasType_strengthening {Γ : TyEnv α β} {M M' : Term α β} {T T' : Ty Security} :
 M.HasType  (Γ ++ (M', T')) T ->  M' ∉ M.fvfn -> M.HasType Γ T
axiom hasType_weakening {Γ : TyEnv α β} {M M' : Term α β} {T T' : Ty Security} :
 M.HasType Γ T -> WF (Γ ++ (M', T')) -> M.HasType (Γ ++ (M', T')) T


axiom strengthening {Γ : TyEnv α β}
        (P: Process α β (Ty Security)) (M : Term α β) (T : Ty Security) :
        P.WellTyped (Γ ++ (M, T)) -> M ∉ P.fvfn -> P.WellTyped Γ
axiom weakening {Γ : TyEnv α β} {M : Term α β} {T : Ty Security}
        (P: Process α β (Ty Security)) :
        P.WellTyped Γ -> WF (Γ ++ (M, T)) -> P.WellTyped (Γ ++ (M, T))
axiom substitution {Γ : TyEnv α β} {x M: Term α β} {T : Ty Security}
                   (P: Process α β (Ty Security)) :
                   P.WellTyped (Γ ++ (x, T)) -> M.HasType Γ T -> (P.subst x M).WellTyped Γ

-- Since the rule for Equiv are not changed, the proof of subject congruence is the same as for Pi (here it is assumed)
axiom subject_congruence {Γ : TyEnv α β} (P Q : Process α β (Ty Security)) (ht : P.WellTyped Γ) (hr : P.Equiv Q) : Q.WellTyped Γ

/-! ## Subtyping -/
section subtyping
  variable {T T': Ty Security}
  /-
    Watchout!
    All lemma in this section have hidden variables, remember to check them, otherwise you migh get suprised by lean's choice and/or failures
  -/

  lemma Ty.Subtype.single: T.Subtype' T' → T.Subtype T' := Relation.ReflTransGen.single

  lemma level_subtyping: T.Subtype T' -> T.l ⊑ T'.l := by
    intros hs
    have := Relation.ReflTransGen.lift _ level_subtyping' hs
    have := Relation.reflTransGen_eq_self @can_flow_refl @can_flow_trans
    simp_all only
    where
      level_subtyping' (T T' : Ty Security) (hs: T.Subtype' T') : T.l ⊑ T'.l := by
        cases hs <;> try (first| exact can_flow_refl | assumption)

  lemma l_subtyping: T.Subtype T.l := by
    cases T with -- by simple case analysis
    | Level => rfl
    | Channel =>
      apply_rules [Ty.Subtype.single, Ty.Subtype'.Channel] -- spams `apply` with the given rules (can close using `assumption`)
    | Key =>
      apply_rules [Ty.Subtype.single, Ty.Subtype'.Key]

  lemma subtype_LLc (h: T.l.c ⊑c .L): T.Subtype LL := by
    trans -- first T ≤ T.l, then T.l ≤ LL
    · apply l_subtyping -- closing this goal let lean know what middle term we should use for
                        -- transitivity: I will be whichever term can `?m******` be replaced with
                        -- to close the goal
    · apply_rules [Ty.Subtype.single, Ty.Subtype'.CanFlow]
      and_intros
      · cases h₀: T.l.c <;> rw[h₀] at h
        contradiction
      · cases T.l.i <;> simp [can_flow_integrity]
end subtyping

/-! ## Lemmas about keys  -/
section key_props
  variable {Γ: TyEnv α β} {N K M: Term α β} {μ μ: KeyKind} {ℓ ℓ': Security} {T T': Ty Security}
  /- Watchout for variables! -/

  lemma hastype_wf (h: M.HasType Γ T): WF Γ := by induction h <;> assumption

  /- Things in a WF environement are either name or variables (as expresssed by `Term.isNameOrVar`) -/
  lemma wf_Γ_name_or_var (hwf: WF Γ) (inΓ: Γ[N]? = some T): N.isNameOrVar := by
    induction hwf with
    | Empty => simp_all
    | Env hnv _ hin _ _ ih =>
      rename Term _ _ => M
      by_cases heq:(N = M)
      · subst heq; assumption -- I will often use `cases` instead of `subst`, because, for our use (i.e. mostly induction tricks),
                              -- it seems to be more successful. But on equalities, they do basically the same things.
                              -- `subst` is "smarter" in some situations, while `cases` is lower level
      · apply ih
        rw[TypingEnvironment.get_reduce] at inΓ <;> assumption

  lemma get_subtypes (inΓ: Γ[M]? = some T) (hht: M.HasType Γ T'): T.Subtype T' := by
      induction hht with
      | Atom =>  simp_all [subtype_refl]
      | Subsumption _ h ih =>
        trans -- `trans` calls the relevant lemma tagged with `@[trans]`.
              -- in this case it is `Relation.ReflTransGen.trans` from `mathlib`. (but the specific lemma doesn't really matter)
        apply ih; assumption; assumption
      | _ => -- elements of the typing environement must be names or variable, this isn't the case here
        exfalso -- so this is absurd (the `exfalso` turns our goal into `False`, it is not needed, but it makes the proof more explicit)
        rename TyEnv _ _ => Γ
        have : WF Γ := by apply hastype_wf; assumption
        have := wf_Γ_name_or_var this (by assumption)
        cases this

  lemma subtype_key (hneq: ℓ ≠ LL) (hst: T.Subtype (μ𝐾'ℓ⟦T'⟧)): T = μ𝐾'ℓ⟦T'⟧ := by
    generalize heq: μ𝐾'ℓ⟦T'⟧ = T₀ at hst -- due to how the `induction` tactic is implemented, lean doesn't want variable in the
    induction hst with                   -- term to apply induction on. Hence we use `generalize` to spawn a new variable `T₀` with
    | refl => rfl                        -- an hypothesis `μ𝐾'ℓ⟦T'⟧ = T₀`. You will see this pattern often in this file unfortunatly
    | tail h ih =>
      cases heq -- we "undo" the `generalize` (destruct the only constuctor of equality)
      cases ih; contradiction

  lemma high_keys (h: N.HasType Γ (μ𝐾'HH⟦T⟧)): Γ[N]? = some (μ𝐾'HH⟦T⟧) := by
    generalize heq: μ𝐾'HH⟦T⟧ = T' at h
    induction h with
    | Atom => cases heq; assumption
    | Subsumption h hst ih =>
      cases heq
      apply subtype_key at hst
      · cases hst
        apply ih; rfl
      · trivial
    | _ => simp_all

  lemma wf_keys (hwf: WF Γ) (hin: Γ[N]? = some (μ𝐾'ℓ⟦T'⟧)): ℓ = HH ∧ μ ∈ [KeyKind.Sym, KeyKind.Dec, KeyKind.Sig] := by
    induction hwf with
    | Empty => simp_all
    | Env _ _ _ _ h ih =>
      rename Term _ _ => M
      by_cases h₀:(N = M) /- `by_cases h:H` split the proof into `H` and `¬H`. If your `H` isn't decidable it will pull `Classical.propDecidable`.
                              Equality on `Term α β` is decidable for us though, so we will not open the phylosophical debate of which axioms you want to use ^^'
                              (`Term` is simple enough that lean can derive the proof of decidablility of equality, this is requested using `deriving DecidableEq`
                              when declaring the type) -/
      · cases h₀; rw[TypingEnvironment.get_append] at hin
        apply h; cases hin; rfl
      · apply ih
        rw[TypingEnvironment.get_reduce] at hin
         <;> assumption

  lemma private_keys (h: N.HasType Γ (μ𝐾'ℓ⟦T⟧)) (hμ: μ.isSec := by simp): ℓ = LL ∨ ℓ = HH := by
    generalize heq: μ𝐾'ℓ⟦T⟧ = T' at h             --           ^^^^^^^^
    induction h with                              -- This is a default parameter, it will be used if we don't specify it when cally `private_keys`
    | Atom =>
      cases heq
      have := wf_keys (by assumption) (by assumption) -- because I'm too lazy to name things
      right; exact this.1
    | Subsumption _ hst ih =>
      cases heq; by_cases heq:(ℓ = LL)
      · left; assumption
      · apply ih; symm; apply subtype_key
          <;> assumption
    | _ =>  cases heq <;> cases hμ

  lemma public_key (h: N.HasType Γ (μ𝐾'ℓ⟦T⟧)) (hk: μ.isPub := by simp): ℓ = LL ∨ ℓ = LH := by
    generalize heq: μ𝐾'ℓ⟦T⟧ = T' at h
    induction h with
    | Atom =>
      cases heq; exfalso
      have := wf_keys (by assumption) (by assumption)
      cases hk <;> simp at this
    | Subsumption _ hst ih =>
      cases heq; by_cases heq:(ℓ = LL)
      · left; assumption
      · apply ih; symm; apply subtype_key
          <;> assumption
    | EncKey | VerKey  =>
      obtain (h|h) := private_keys (by assumption) -- no need to call `by simp`, lean does it on its own !
        <;> cases heq <;> cases h
      · left; rfl
      · right; rfl
    | _ => cases heq

  lemma low_keys_private (h: N.HasType Γ (μ𝐾'LL⟦T⟧)) (hk: μ.isSec := by simp): T = LL := by
    generalize heq: μ𝐾'LL⟦T⟧ = T' at h
    induction h with
    | Atom =>
      cases heq
      have := wf_keys (by assumption) (by assumption)
      cases hk <;> simp at this
    | Subsumption _ hst ih =>
      induction hst
      · apply ih; assumption
      · rename_i h ih'
        cases heq; cases h; rfl
    | _ => cases heq <;> cases hk

  lemma low_keys (h: N.HasType Γ (μ𝐾'LL⟦T⟧)): T = LL := by
    generalize heq: μ𝐾'LL⟦T⟧ = T' at h
    induction h with
    | Atom =>
      cases heq
      have := wf_keys (by assumption) (by assumption)
      cases this.1
    | Subsumption _ hst ih =>
      induction hst
      · apply ih; assumption
      · rename_i h ih'
        cases heq; cases h; rfl
    | VerKey h | EncKey h =>
      cases heq
      obtain (h|h) := private_keys h <;> cases h
      apply low_keys_private h
    | _ => cases heq

  lemma impossible_mutliple_ht_key (hht: K.HasType Γ (μ𝐾'LL⟦T⟧)) (hht': K.HasType Γ (μ'𝐾'HH⟦T'⟧)): False := by
    apply high_keys at hht'
    have := get_subtypes (by assumption) (by assumption)
    apply level_subtyping at this
    cases this.1

  lemma uniqueness_of_keys' (hμ: μ.isSec := by simp) (hht: K.HasType Γ (μ𝐾'ℓ⟦T⟧)) (hht': K.HasType Γ (μ'𝐾'ℓ⟦T'⟧)):
      T = T' := by
      obtain (h|h) := private_keys hht (by assumption) -- `simp` doesn't look in the hypothesis, hence we need to explicitly state `hμ` argument
          <;> cases h
      · apply low_keys at hht; apply low_keys at hht'; simp_all only []
      · apply high_keys at hht; apply high_keys at hht'; simp_all

  lemma uniqueness_of_keys (hht: K.HasType Γ (μ𝐾'ℓ⟦T⟧)) (hht': K.HasType Γ (μ'𝐾'ℓ'⟦T'⟧))
                           (hμ: μ.isSec := by simp) (hμ': μ'.isSec := by simp):
                              T = T' ∧ ℓ = ℓ' := by
      obtain (h|h) := private_keys hht (by assumption) <;> cases h
       <;> obtain (h|h) := private_keys hht' (by assumption) <;> cases h
      · and_intros; aapply uniqueness_of_keys' (α:=α) (β:=β) hμ; rfl -- `aaplly` tries to call `assumption`
      · exfalso; aapply @impossible_mutliple_ht_key α β
      · exfalso; aapply @impossible_mutliple_ht_key α β
      · and_intros; aapply uniqueness_of_keys' (α:=α) (β:=β) hμ; rfl
end key_props

/-! ## Lemmas about payloads -/
section payload_props
  variable {Γ: TyEnv α β} {N K M: Term α β} {μ μ: KeyKind} {ℓ ℓ': Security} {T T': Ty Security}

    /-
      `trivial` is an extensible tactic that calls other tactics. This is designed to easily dispach trivial goals.

      By default it includes things like `rfl`, `assumption`, `contradiction` or some *very* dumb boolean reasoning.

      We extend it here to dispach trivial `Atom` goals on non variable objects
    -/
    macro_rules
    | `(tactic| trivial) => `(tactic| cases (wf_Γ_name_or_var (by assumption) (by assumption)); done)
          -- the `done` at the end ensures taht we are not left in a weird state, where the tactic succeeds but doesn't close the goal


  lemma payload_senc (htc: (M.SEnc K).HasType Γ T') (htk: K.HasType Γ (Sym𝐾'ℓ⟦T⟧)): M.HasType Γ T := by
    generalize heq: M.SEnc K = M₀ at htc
    induction htc with
    | Atom => cases heq; trivial
    | Subsumption _ _ ih => aapply ih
    | SymEnc htk' h ih ih' =>
      cases heq
      rename_i  ℓc ℓi T; rename Ty _ => T'
      have : T' = T :=  (uniqueness_of_keys htk' htk).1 -- here we use our default parameters
      cases this; assumption
    | _ => cases heq

  lemma payload_aenc (htc: (M.AEnc (K.Ek)).HasType Γ T') (htk: K.HasType Γ (Dec𝐾'ℓ⟦T⟧)): M.HasType Γ T ∨ (T'.l.i = .L ∧ M.HasType Γ LL) := by
    generalize heq: (M.AEnc (K.Ek)) = M₀ at htc
    induction htc with
    | Atom => cases heq; trivial
    | Subsumption _ hst ih => -- there has to be a better way, but this works ^^'
        obtain (h|⟨hl, hht⟩) := ih htk heq
        · left; assumption
        · right; and_intros
          · induction hst with
            | refl => assumption
            | tail _ h ih =>
              rename_i T T' _ _ b c a;
              rcases T with (⟨_,_⟩|⟨⟨_, _⟩, _⟩|⟨_,⟨ _, _⟩, _ ⟩) <;> cases hl
               <;> rcases b with (⟨_,_⟩|⟨⟨_, _⟩, _⟩|⟨_,⟨ _, _⟩, _ ⟩) <;> cases ih
               <;> cases h -- oh yeaaah, 15 goals! praise the computer!
              all_goals try rfl -- most of them are trivial
              all_goals ( -- the rest is solved by even more bruteforcing!
                rename _ ⊑ _ => h; rename Security => ℓ
                obtain ⟨_, h⟩ := h
                rcases ℓ with ⟨_, (_|_)⟩ <;> cases h; simp)
          · assumption
    | AsymEnc htk' htm ihk ihm =>
      cases heq
      obtain (h|h) := public_key htk' (by simp) <;> cases h
      · have := low_keys (by assumption); cases this
        right; and_intros <;> trivial
      · generalize heq₁ : K.Ek = K₀ at htk'; generalize heq₂ : Enc𝐾'LH⟦_⟧ = T₀ at htk' -- this is ridiculous
        induction htk' with
        | Atom => cases heq₁; cases heq₂; trivial
        | Subsumption h hst ih =>
          aapply ih; cases heq₁; cases heq₂
          apply subtype_key at hst
          · cases hst; rfl
          · trivial
        | EncKey htk' _ =>
          cases heq₁; cases heq₂
          have :=  (uniqueness_of_keys htk' htk).1
          cases this; left; assumption
        | _ => cases heq₁
    | _ => cases heq

  lemma payload_sign (hts: (M.Sign K).HasType Γ T') (htk: K.HasType Γ (Sig𝐾'ℓ⟦T⟧)): M.HasType Γ T ∧ T.l.c ⊑c T'.l.c := by
    generalize heq: (M.Sign K) = M₀ at hts
    induction hts with
    | Atom => cases heq; trivial
    | Subsumption _ hst ih =>
      induction hst with
      | refl => aapply ih
      | tail _ h ih' =>
        obtain ⟨ih₁, ih₂⟩ := ih'
        cases h <;> try (simp_all; done) -- dispach almost trivial goals
        and_intros; assumption
        rename _ ⊑ _ => h
        obtain ⟨hc, _⟩ := h
        trans <;> assumption -- NB: transitivity on `⊑c` wasn't proven for the π-calculus
                             -- This calls the corresponding lemma tagged with `trans`
                             -- (that's `can_flow_confidentiality_trans` here)
    | DigSig htk' _ _ _ =>
      cases heq
      obtain ⟨heqT, heqℓ⟩ := (uniqueness_of_keys htk' htk)
      cases heqT; cases heqℓ
      and_intros
      · assumption
      · simp_all; rfl
    | _ => cases heq

  lemma payload_signT  (hts: (M.Sign K).HasType Γ T') (htk: K.HasType Γ (Sig𝐾'ℓ⟦T⟧)): M.HasType Γ T :=
     (payload_sign hts htk).1
end payload_props

/-! ## Miscalenious lemmas -/
section extra_lemmas
  variable {Γ: TyEnv α β} {N K M: Term α β} {μ μ: KeyKind} {ℓ ℓ': Security} {T T': Ty Security}

  lemma rev_ver_key_LH (hht: K.Vk.HasType Γ (Ver𝐾'⟨.L,.H⟩⟦T⟧)) : K.HasType Γ (Sig𝐾'⟨.H,.H⟩⟦T⟧) := by
    have hht := hht;
    generalize heqk: K.Vk = K₀ at hht; generalize heqtk: (Ver𝐾'⟨_,_⟩⟦T⟧) = T₀ at hht;
    induction hht with
    | Atom => cases heqk; trivial
    | VerKey =>
      cases heqk; cases heqtk
      obtain (h|h) := private_keys (by assumption) <;> cases h
      assumption
    | Subsumption h hst ih =>
      cases heqk; cases heqtk; specialize ih hht rfl
      obtain (hℓ|hℓ) := public_key hht <;> cases hℓ
      apply subtype_key (by trivial) at hst; cases hst
      aapply ih rfl
    | _ => cases heqk

  lemma rev_ver_key (hht: K.Vk.HasType Γ T): ∃ ℓ' T', K.HasType Γ (Sig𝐾'ℓ'⟦T'⟧) := by
    generalize heqk: K.Vk = K₀ at hht
    induction hht with
    | Atom => cases heqk; trivial
    | VerKey => cases heqk; tauto
    | Subsumption _ _ ih => aapply ih
    | _ => cases heqk

end extra_lemmas

/-!
## Soundness results
These are the main results
-/

/--
Subject reduction has to handle the NonceCheck and Destr cases
The rest of the cases are identical to the Pi proof
-/
lemma subject_reduction
  {Γ : TyEnv α β}
  (P Q : Process α β (Ty Security))
  (ht : P.WellTyped Γ)
  (hr : P.Reduce Q)
: Q.WellTyped Γ := by
  induction hr generalizing Γ with
  | IO => cases ht; case IO.Par owt iwt =>
     constructor
     · cases owt; assumption
     · apply substitution
       · cases iwt; assumption
       · cases owt; cases iwt
         rename_i _ ht _ _ _ ht' _
         have := uniqueness_channel_types Γ _ ht ht'
         simp_all only [Ty.Channel.injEq]
  | Par => cases ht; tauto
  | Res => cases ht; case Res.Res a1 a => constructor; apply a1; trivial
  | @Struct P Q P' Q' _ a1 a ih  =>
    have := subject_congruence P' P ht (by constructor; tauto)
    exact subject_congruence Q Q' (ih this) a
  | Cond2 => cases ht <;> assumption
  | @Cond1 M N =>
    cases ht; assumption
    case Cond1.NonceCheck T T' n  nle hn hT inΓ ih =>
      exfalso -- this is impossible
      aapply nle; clear ih nle
      induction inΓ with
      | Atom _ heq =>
        cases hn; rw[hT] at heq; cases heq -- cleanup equalities
        rfl -- close
      | Subsumption _ hst ih =>
        rename_i T₁ _
        apply level_subtyping at hst
        specialize ih  hn hT
        trans <;> assumption
      | _ => cases hn /- the rest impossible bc of `hn` -/
  | @Destr D M K M' x P hdestr =>
    cases ht with -- in growing order of difficulty
    | @SymDec =>
      aapply substitution
      cases hdestr
      aapply payload_senc
    | AsymDec hht hhtk hwt hwtL =>
      cases hdestr
      obtain (hT|⟨hℓ, hT⟩) := payload_aenc (by assumption) (by assumption)
      · aapply substitution
      · apply substitution -- My homebrewed `aapply` fails here because it choses the wrong hypothesis. Thus we fall back to `apply`
        aapply hwtL
        assumption
    | SignCheck => -- we cannot use `payload_sign` directly here, we need to work first
      aapply substitution; cases hdestr
      obtain (hℓ | hℓ) := public_key (by assumption) (by simp)
        <;> cases hℓ
        <;> rename_i T' hPwt K ht hℓc htk
      · -- case LL
        cases (low_keys (by assumption))
        obtain ⟨ℓK, Tk, hk⟩ := rev_ver_key htk
        obtain ⟨hℓ, hT⟩ := payload_sign ht hk
        aapply Term.HasType.Subsumption
        aapply subtype_LLc
        cases h: T'.l.c
        · rw[h] at hT; assumption
        · apply hℓc at h; contradiction
      · -- cases HH
        apply rev_ver_key_LH at htk
        obtain ⟨hℓ, _⟩ := payload_sign ht htk
        assumption


section ManyNew
  /-- Chains `new`s. Stands for `new \tidle{a}` in the paper -/
  def manyNew (as: List (β × τ)) (p: Process α β τ) :=
    List.foldr (λ (a, T) p => .New a T p) p as

  abbrev mkEnv : TyEnv α β -> List (β × Ty Security) -> TyEnv α β :=
    List.foldl (fun g x => g ++ (@Term.Name α β x.1, x.2))

  lemma manyNew_well_typed {Γ : TyEnv α β} (h: (manyNew as P).WellTyped Γ) : P.WellTyped (mkEnv Γ as) := by
    rcases as with (_|⟨hd,tl⟩)
    · tauto
    · have : ∀ a T, manyNew ((a,T)::tl) P = .New a T (manyNew tl P)  := by tauto
      rw[this] at h; cases h; rename_i a
      apply manyNew_well_typed a

  variable (Γ Γ' : TyEnv α β) (bs : List (β × Ty Security)) (hd : (Term α β × Ty Security))
  axiom tyEnv_mkEnv_perm: List.Perm (mkEnv (Γ ++ hd) bs) ((mkEnv Γ bs) ++ hd)
  axiom hasType_perm_iff (t: Term α β) (T: Ty Security) (h: List.Perm Γ Γ'): t.HasType Γ T ↔ t.HasType Γ' T
  axiom processWellTyped_perm_iff (P : Process α β (Ty Security)) (h: List.Perm Γ Γ'): P.WellTyped Γ ↔ P.WellTyped Γ'
end ManyNew

/--
This is the same theorem as before, note that in the new language we can not
only send names but also other therms (e.g., encrypted data) so this theorem
states that every **nonce** that is sent is not secret.
-/
theorem secrecy  {Γ : TyEnv α β} (P O P' P'' : Process α β (Ty Security)) :
  (∀ T, (d,T) ∉ bs) -> (∀ T, (b,T) ∉ bs) -> (d ≠ b) ->
  (P.Par O).WellTyped Γ ->
  (P.Par O).Reduce (.New d T (.New b Tb (manyNew bs (P'.Par (.Out (.Name b) (.Name d) P''))))) ->
  T.l.c ⊑c Tb.l.c
  := by
     introv _ _ _ wt this
     replace := subject_reduction _ _ wt this
     rcases this with (_|_|_|⟨(_|_|_|⟨this⟩)⟩)
     replace := manyNew_well_typed this
     rcases this with (_|⟨a,(_|_|_|_|_|_|⟨pwt,mt,ct⟩)⟩)
     have hperm: List.Perm (mkEnv (Γ ++ (Term.Name (α:= α) d, T) ++ (Term.Name (α:= α) b, Tb)) bs) ((mkEnv Γ bs) ++ (Term.Name (α:= α) d, T) ++ (Term.Name (α := α) b, Tb)) :=
      by apply List.Perm.trans (by apply tyEnv_mkEnv_perm ); apply List.Perm.cons; apply tyEnv_mkEnv_perm
     simp_all only [ne_eq]
     rw[hasType_perm_iff (h:=hperm)] at *
     rw[processWellTyped_perm_iff (h:=hperm)] at *
     clear hperm
     have := channel_levels _ _ ct
     rcases this with (_|⟨_,(_|⟨a⟩)⟩)
     · have := low_channels _ ct
       rcases pwt with (⟨pwf,pget⟩|⟨pht,psub⟩)
       · simp_all; cases (Tb.l.c) <;> simp [can_flow_confidentiality]
       · generalize hΓ: (mkEnv Γ bs ++ (@Term.Name α β d, T) ++ (@Term.Name α β b, Tb)) = Γ' at pht
         generalize hd: @Term.Name α β d = D at pht
         induction' pht with _ _ _ _ _ _ _ _ _ _ _ a_ih
         · have := level_subtyping psub
           simp [can_flow, can_flow_confidentiality, reduceCtorEq, imp_self, implies_true, *] at this
           split at this <;> simp_all [can_flow_confidentiality]
           split <;> try simp
           rename Term α β => M;
           rename Ty Security => T₁
           have : T = T₁ := by aesop
           simp_all
         · apply a_ih; apply subtype_trans <;> assumption
           all_goals assumption
         all_goals simp_all
     · have := high_channels _ ct
       cases (T.l.c) <;> simp_all [can_flow_confidentiality]
     · contradiction


instance : Decidable (ℓ ⊑i ℓ') := by
  have := instDecidableTrue
  have := instDecidableFalse
  cases ℓ <;> cases ℓ' <;> simpa[can_flow_integrity]


/-- The integrity label of a `Term` -/
abbrev ℒi (Γ : TyEnv α β) : Term α β -> Level
| .Ek K | .Vk K => ℒi Γ K
| .SEnc M K | .AEnc M K | .Sign M K =>
  match Γ[K]? with
  | some (_μ𝐾'⟨.H,.H⟩⟦T⟧) => if ℒi Γ M ⊑i T.l.i then .H else .L
  | _ => .L
| M@(.Name _) | M@(.Var _) =>
  match Γ[M]? with
  | some ℓ => ℓ.l.i
  | none   => .L

/-- If a process is well typed, then it preserves intergity -/
theorem integrity₁ {Γ : TyEnv α β} (P O P' P'' : Process α β (Ty Security))
  (hns: ∀ T, (k,T) ∉ bs)  -- prevents shadowing/α-renaming issues
  (hwt: (P.Par O).WellTyped Γ) -- P | O is well typed
  -- intergrity properity
  (hd: MK.Destruct dk (.Name K) M)
  (hred: ((P.Par O).Reduce ((.New k (μ𝐾'HH⟦Tb⟧) (manyNew bs (P'.Par (.CaseOf dk MK x (.Name k) P''))))))):
  ∃ Γ₁, ℒi Γ₁ M ⊑i Tb.l.i
  := by
    cases hl: Tb.l.i with
    | L => exists Γ
    | H =>
    aapply subject_reduction at hred; clear hwt
    obtain (_|_|_|⟨hwt⟩) := hred
    aapply manyNew_well_typed at hwt
    obtain (_|⟨hP', (_|_)⟩) := hwt <;> cases hd
    case AsymEnc ℓc ℓi T T' h₁ h₂ _ hT =>
      exfalso -- impossible
      sorry
    sorry
    -- WIP
