import Mathlib.Tactic

section SecurityLevels

/-- Defines the two possible security levels High and Low --/
inductive Level where | L | H
deriving Repr, DecidableEq

/--
Defines the standard Security preorder as a pair specifying separately secrecy and integrity:
```
    HL
   /  \
  /    \
HH      LL
  \    /
   \  /
    LH
```
where, for instance HH represents high confidentiality and high integrity.
-/
structure Security where
  c: Level
  i: Level
  deriving Repr, DecidableEq

def can_flow_confidentiality : Level -> Level -> Prop
  | .H, .L => False
  | .L, .L => True
  | _, .H => True
infix:50 " ⊑c " => can_flow_confidentiality

def can_flow_integrity : Level -> Level -> Prop
  | _, .L => True
  | .L, .H => False
  | .H, .H => True
infix:50 " ⊑i " => can_flow_integrity

def can_flow (ℓ₁ ℓ₂ : Security) : Prop := ℓ₁.c ⊑c ℓ₂.c ∧ ℓ₁.i ⊑i ℓ₂.i
infix:50 " ⊑ " => can_flow


@[refl]
lemma can_flow_refl : a ⊑ a := by
  rcases a with ⟨(_|_), (_|_)⟩
  <;> simp_all [can_flow, can_flow_confidentiality, can_flow_integrity]

@[trans]
lemma can_flow_trans : a ⊑ b -> b ⊑ c -> a ⊑ c := by
  intros ab bc
  simp_all [can_flow, can_flow_confidentiality, can_flow_integrity]
  rcases a with ⟨ca, ia⟩
  rcases b with ⟨cb, ib⟩
  rcases c with ⟨cc, ic⟩
  cases ca <;> cases cb <;> cases cc <;>
  cases ia <;> cases ib <;> cases ic <;> trivial

@[trans]
lemma can_flow_confidentiality_trans: a ⊑c b → b ⊑c c → a ⊑c c := by
  cases a <;> cases b <;> cases c <;> simp [can_flow_confidentiality] -- too lazy to think

@[refl]
lemma can_flow_confidentiality_refl: a ⊑c a := by
  cases a <;> simp [can_flow_confidentiality]



instance : Decidable (ℓ ⊑c ℓ') :=
  if h: ℓ = .H ∧ ℓ' = .L then isFalse (by simp_all[can_flow_confidentiality])
  else isTrue (by cases ℓ <;> cases ℓ' <;> simp_all[can_flow_confidentiality])

instance : Decidable (ℓ ⊑i ℓ') :=
  if h: ℓ = .L ∧ ℓ' = .H then isFalse (by simp_all[can_flow_integrity])
  else isTrue (by cases ℓ <;> cases ℓ' <;> simp_all[can_flow_integrity])

instance {T T': Security} : Decidable (T ⊑ T') :=
  if h: T.c ⊑c T'.c ∧ T.i ⊑i T'.i then isTrue (by simpa[can_flow]) else isFalse (by simp_all[can_flow])



end SecurityLevels
