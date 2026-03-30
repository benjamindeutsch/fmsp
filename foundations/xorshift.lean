/-! # Set up -/

/--
  The resolution (bit-width) we will be working with.
  We use 64-bit values for the xorshift128+ algorithm. -/
def precision : Nat := 64

/--
  XorShiftState is the internal state of the xorshift128+ algorithm.
  It consists of a pair of 64-bit values `(state0, state1)`. -/
def XorShiftState := (BitVec precision × BitVec precision)

/-!
  The following namespace organizes definitions under the XorShiftState prefix.
  See: https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/ -/
namespace XorShiftState
  /-
    Variable declares parameters for all definitions in this scope. Useful for
    theorems that take s, s' as parameters. See: https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#section-variables
    If you hover with the mouse on e.g., state0, you see that the actual
    definition is `XorShiftState.state0 (s : XorShiftState) : BitVec precision`
    since the variable s is used in the body of the definition. -/
  variable (s s': XorShiftState)

  /-- Accessor for the first component (`state0`) -/
  @[simp] abbrev state0 := s.1

  /-- Accessor for the second component (`state1`) -/
  @[simp] abbrev state1 := s.2


  /--
    Extensionality theorem: two XorShiftStates are equal iff their components are equal.
    This is a standard theorem for product types.
    The @[ext] attribute allows us to use this lemma via the `ext` tactic -/
  @[ext]
  theorem ext (h₁: s.1 = s'.1) (h₂: s.2 =s'.2) : s = s' := by
    cases s; cases s'
    simp_all [XorShiftState]

  /--
    Define the XOR operation on XorShiftState.
    This applies XOR component-wise to the pair of bit vectors.
    The @[simp] attribute makes this simplify automatically. -/
  @[simp]
  instance : XorOp XorShiftState where
    xor | ⟨s₁₁, s₁₂⟩, ⟨s₂₁, s₂₂⟩ => ⟨s₁₁ ^^^ s₂₁, s₁₂ ^^^ s₂₂⟩

  -- Defines how the XOR operator (^^^) expands on XorShiftState.
  -- This helper simplifies working with XOR notation.
  @[simp]
  theorem xor_def (s₁ s₂: XorShiftState) : s₁ ^^^ s₂ = ⟨s₁.1 ^^^ s₂.1, s₁.2 ^^^ s₂.2⟩  := rfl

end XorShiftState

/--
  The main xorshift algorithm in imperative style.
  This matches the C implementation from V8:
```c
   s1 ^= s1 << 23;
   s1 ^= s1 >> 17;
   s1 ^= s0;
   s1 ^= s0 >> 26;
```
  Uses the Id monad to simulate mutable variables in a pure functional setting. -/
def xorshift (s: XorShiftState) : XorShiftState := Id.run $ do
  let mut s1 := s.state0
  let mut s0 := s.state1
  let state0 := s0
  s1 := s1 ^^^ (s1 <<< 23)
  s1 := s1 ^^^ (s1 >>> 17)
  s1 := s1 ^^^ s0
  s1 := s1 ^^^ (s0 >>> 26)
  let state1 := s1
  return ⟨state0, state1⟩


--------------------------------------------------------------------------------
/-! # Equivalence and rewriting -/

/-- Functional representation of xorshift.
    Each transformation step is explicitly named and non-mutating. -/
def xorshift' (s: XorShiftState) : XorShiftState :=
  let s₀ : XorShiftState := ⟨s.state1, s.state0⟩
  let s₁ : XorShiftState := ⟨s₀.state0, s₀.state1 ^^^ (s₀.state1 <<< 23)⟩
  let s₂ : XorShiftState := ⟨s₁.state0, s₁.state1 ^^^ (s₁.state1 >>> 17)⟩
  let s₃ : XorShiftState := ⟨s₂.state0, s₂.state1 ^^^ s₂.state0⟩
  let s₄ : XorShiftState := ⟨s₃.state0, s₃.state1 ^^^ (s₃.state0 >>> 26)⟩
  s₄

/-- The imperative and functional definitions are equivalent by construction.
    They both implement the same sequence of XOR and shift operations. -/
theorem xorshift_is_xorshift': xorshift = xorshift' := rfl

#print Function.comp

/-- Compositional representation using function composition.
    Each lambda function represents one step of the algorithm.
    The symbol `∘` aliases `Function.comp` denoting function composition, applied right-to-left. -/
def xorshift'' : XorShiftState → XorShiftState :=
    (λ s : XorShiftState => ⟨s.state0, s.state1 ^^^ (s.state0 >>> 26)⟩)
  ∘ (λ s : XorShiftState => ⟨s.state0, s.state1 ^^^ s.state0⟩)
  ∘ (λ s : XorShiftState => ⟨s.state0, s.state1 ^^^ (s.state1 >>> 17)⟩)
  ∘ (λ s : XorShiftState => ⟨s.state0, s.state1 ^^^ (s.state1 <<< 23)⟩)
  ∘ (λ s : XorShiftState => ⟨s.state1, s.state0⟩)

/-- ## TASK 1 (0.5 pts): Prove that functional and compositional representations are equivalent.
    **Hint**: This is true by definition since both are structurally the same computation. -/
theorem xorshift'_is_xorshift'': xorshift' = xorshift'' := by
  sorry

/-- Combines the two equivalences: imperative = functional = compositional. -/
theorem xorshift_is_xorshift'': xorshift = xorshift'' := by
  rw[xorshift_is_xorshift']
  rw[xorshift'_is_xorshift'']


--------------------------------------------------------------------------------
/-! # Extensionality -/

/-- Swaps the two components of an XorShiftState.
    This operation swaps `(state0, state1)` to `(state1, state0)`. -/
def swap_state (s: XorShiftState) : XorShiftState := ⟨s.state1, s.state0⟩

/-- ## TASK 2 (0.25 pts): Prove that swap_state is its own inverse.
    **Hint**: Apply swap_state twice and show you get back the original state.
    Use the `unfold` tactic to expand swap_state, then apply `XorShiftState.ext`
    directly or using the `ext` tactic -/
theorem swap_state_inv : ∀ s, swap_state (swap_state s) = s := by
  sorry

/-- ## TASK 3 (0.25 pts): Prove that shifting by precision left or right is equivalent.
    For any p-bit vector s, shifting right by p equals shifting left by p.
    **Hint**:  Use `ext` to prove bitwise equality. -/
theorem shift_precision : ∀ (p: Nat) (s: BitVec p), s >>> p = s <<< p := by
  sorry


--------------------------------------------------------------------------------
/-! # Linearity -/

/-- A function is linear (with respect to XOR) if it preserves XOR operations.
    That is, applying f to the XOR of two states equals the XOR of the results.
    This is analogous to linearity in vector spaces where `f(a+b) = f(a) + f(b)`. -/
def IsLinear (f: XorShiftState → XorShiftState): Prop :=
  ∀ s₁ s₂: XorShiftState, f (s₁ ^^^ s₂) = (f s₁) ^^^ (f s₂)


/-- ## TASK 4 (0.5 pts): Prove that composition of linear functions is linear.
    **IMPORTANT**: Do NOT use `simp` or `grind` tactics for this proof.
    Only use: `intro`, `apply`, `rw`, `unfold`

    **Hint**: Start by unfolding the IsLinear definition, then unfold `Function.comp`. -/
theorem IsLinear.comp {f g: XorShiftState → XorShiftState}
  (hf: IsLinear f) (hg: IsLinear g) : IsLinear (f ∘ g) := by
    sorry


/-- ## TASK 5 (1.5 pts): Prove that xorshift is linear.
    **Hint**: Use the fact that `xorshift = xorshift''` and apply the composition property.
    You will need to prove that each component function in the composition is linear.
    Apply `ext` and use the `simp` or `grind` tactic to prove the bitwise equalities. -/
theorem xorshiftstate_is_linear: IsLinear xorshift := by
  sorry

/-
  You can test the xorshift function by running `lake exec xorshift-exec`!
-/
def main : IO Unit := do
  let stdin ← IO.getStdin
  IO.println "set the initial seed"
  IO.print "s0: "
  let s0 := (← stdin.getLine).trimAscii.toNat!
  IO.print "s1: "
  let s1 := (← stdin.getLine).trimAscii.toNat!
  let mut state : XorShiftState := ⟨s0, s1⟩

  for _ in [0:10] do
    state := xorshift state
    let n  := (state.state0 + state.state1).toFin
    println! "{n}"
