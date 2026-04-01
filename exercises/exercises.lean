/-
  This files serves as a small library of proofs example to get
  familiar with the many possible symtax of lean.

  We are encourage to replace all the `sorry` by proofs or definitions.
  The solutions are available in the `solution.lean` file.

  The difficulty of the exercises increases progressively. Even if you fail
  an exercise, you are encourage to read the rest of the file as it contains
  various trip and tricks that could be useful for you
-/

/-
### Declarations
  There are many ways to declare lemmas/theorem/functions in lean
-/

-- the 'base' way of defining objects is donne via the `def` keyword
def add (a b: Nat) : Nat := a + b

/- Lemmas can be declared using the `theorem` keyword. When mathlib
  is in scope, we will also use the keyword `lemma` interchangeably -/
theorem add1 (a: Nat): a + 1 = Nat.succ a := by rfl

-- `example` lets us skip the name
example : a + 1 = Nat.succ a := by rfl

/- we can also use `def` to declare theorems because all declarations are `def`s
 with possibly some preprocessing glued to it -/
def add1' (a: Nat): a + 1 = Nat.succ a := by rfl

namespace test
  /-
    the keyword `namespace` lets us avoid name colisions. Everything declared
    here will have to be called outside the block using `test.*`.
  -/

  def add1 (a: Nat):  Nat.succ a = a + 1 := by rfl
  #check add1
end test
#check test.add1
-- note the distinction with the `add1` we defined earlier
#check add1

/- **TIP**: in vscode hoovering over a definition not only gives its full type, but
            also its full name! -/

namespace Basics
  theorem e1 (A B: Prop) : A → B → A := by
  /-                         ^
    in vscode you can write `→` by typing `\to`, it is equivalent to `->` in general
    hoovering over 'weird' symbol will tell you a way to write it -/
    intro ha hb -- <- introduce variable and/or hypothesis to the environement
    apply ha

  -- we can prove/express this statement in many different ways

  -- pre-introduced hypothesis
  theorem e2 (A B: Prop) (ha: A): B → A := by
    intro hb
    apply ha
  -- the `exact` tactic succeeds only when the goal *is* `ha`
  theorem e3 (A B: Prop) (ha: A) (hb: B): A := by exact ha
  /- an interesting tactic is `exact?`. Lean will search
     all the theorem it knows to check if the goal has already been proven.
     It gives the result of its search in the infoview -/
  theorem e4 (A B: Prop) (ha: A) (hb: B): A := by exact?
  /- with the Curry–Howard correspondence, proofs are functions, so we can
     write the function directly -/
  theorem e5 (A B: Prop) (ha: A) (hb : B): A := ha

  -- similarily we can `print` a proof and see what lean built
  #print e1
  #print e5

  -- `assumption` will look for anything in the hypothesis to close the goal with
  theorem e6 (A B: Prop) (ha: A) (hb: B): A := by assumption

  -- closes trivial goals by using simple tactics like `assumption` or `contradiction`
  theorem e7 (A B: Prop) (ha: A) (hb: B): A := by trivial
end Basics



namespace Equality
  -- lets define equality as it is defined in lean

  inductive MEq {α}: α → α → Prop where
  | refl (a:α): MEq a a
  -- That is, the only way to build a proof of `MEq` is using reflexivity.

  #print Eq -- This is lean's equality
  #print MEq

  variable {a:Type} (x y z:α)
  /-^^^^^^^^^^^^^^^
    `α` will be a (hidden) paramenter to all declarations using it.
    Similarily `x`, `y` and `z` will be automatically included as paramenters to
    the declaration using them.

    This hold for the whole namespace `Equality`
  -/

  theorem refl: MEq x x := by exact MEq.refl x
  -- Note that `refl` has indeed the type `(x:α) → MEq x x` as expected
  #check refl
  /- you can also check this by hoovering over an identifier. Hoovering over
     identifier in a good habits as it exposes most of lean's "magic" -/

  theorem symm (h: MEq x y): MEq y x := by
    cases h with
    | refl =>
      apply MEq.refl -- <- we only have one case

  section exercices
    theorem trans (h1: MEq x y) (h2: MEq y z): MEq x z := by
      cases h1 with
       | refl =>
        cases h2 with
        | refl =>
          apply MEq.refl

    theorem subst (P: α → Prop) (h: MEq x y): P x →  P y := by
      intro hp
      cases h with
      | refl => apply hp

    #check Iff.intro -- this can split a `↔` into two proofs of `→`
    theorem meq_iff_eq: MEq x y ↔ x = y := by
      apply Iff.intro
      intro ha
      cases ha with
       | refl => rfl
      intro hb
      subst hb
      apply refl

  end exercices

end Equality


namespace RecordAndInductive
  /- Outside of `def` it is possible to define 'inductive' type/props and record type/prop -/

  -- ### inductive

  inductive List (α:Type): Type where
  | nil: List α
  | cons (hd: α) (tl: List α): List α
  /- This is the  equivalent of 'enum's in other languages -/

  /- It is also possible to define Proposition inductively too -/
  inductive Even: Nat → Prop where
  | zero: Even 0
  | even_plus_2 (k:Nat) (hk: Even k): Even (k+2)
  /- This is a property that can only be proven with those two constructors.
     This maps to sets of rules in regular mathematics -/

  -- ### record types
  /- The sort of dual of inductive types are record types. They correspond to `struct`s in
     other programming language -/

  structure Point: Type where
    x: Nat
    y: Nat

  -- then we can build a point in many ways:
  def p1: Point := {x:=1, y:=2}
  def p2: Point where
    x := 1
    y := 2
  def p3: Point := ⟨1, 2⟩
  def p4 := Point.mk 1 2 -- auto generated function by lean
  #print p1
  #print p2
  #print p3
  #print p4
  /- Note that lean needs to know the type of the object to build it
     hence the type annotations for `p1`, `p2` and `p3` -/

  /- we can also have proofs/propositions in our record -/
  structure Fin (n:Nat) where
    val: Nat
    lt: val < n
  /- this type represent the natural numbers smaller than `n`. The `lt` field doesn't
     contain data, but a proof that `val` is small enough. -/
  #check Fin.mk
  def fin1: Fin 10 where
    val := 5
    lt := by omega -- powerful tactic for arithmetics
  def fin2: Fin 10 := ⟨5, by omega⟩

  /- `Point.x` and `Point.y` are the projection operators
    of `Point` -/
  #check Point.x
  #check Point.y
  example (x y:Nat): Point.x {x, y} = x := by rfl
  example (x y:Nat): Point.y {x, y} = y := by rfl

  section exercices
    namespace Point
      /-- define the pointwise addition such that `addx` and `addy` hold -/
      def add (p1 p2: Point): Point :=
        ⟨p1.x+p2.x, p1.y+p2.y⟩
    end Point
  end exercices

  theorem addx (p1 p2: Point):
    Point.x (Point.add p1 p2) = (Point.x p1+ Point.x p2) := by simp [Point.add]
  theorem addy (p1 p2: Point):
    (p1.add p2).y = (p1.y + p2.y) := by simp [Point.add]
  /- Notice the notations. A element brings its type in scope when using `.`. -/
end RecordAndInductive

namespace Logic
  -- We have enough to rebuild the connective of propositionnal logic now !

  inductive MTrue: Prop where
  | mtrue : MTrue

  inductive MFalse: Prop where
  /- well... this is a type that can't be built, therefore it has no constructors.  -/

  inductive MOr (A B: Prop): Prop where
  | left (ha: A): MOr A B
  | right (hb: B): MOr A B

  structure MAnd (A B:Prop): Prop where
    left: A
    right:B

  variable (A B: Prop)

  theorem mand_is_and: MAnd A B ↔ A ∧ B := by
    apply Iff.intro
      <;> rintro ⟨left, right⟩-- <- introduce and do case analysis (1 case only)
    · and_intros -- <- split an `and` in many subgoals
      all_goals assumption -- <- apply a tactic to all visible goals
    · -- exact { left := left, right := right } -- or
      exact { left, right }

  section exercises
    example: MTrue ↔ True := by
      apply Iff.intro
      · intro ha
        apply True.intro
      · intro hb
        apply MTrue.mtrue

    example: MFalse ↔ False := by
      apply Iff.intro
      intro ha
      contradiction
      intro hb
      cases hb

    example: MOr A B ↔ A ∨ B := by
      apply Iff.intro
      · intro ha
        cases ha with
        | left ha' => exact Or.inl ha'
        | right hb' => exact Or.inr hb'
      · intro hb
        cases hb with
        | inl ha' => exact MOr.left ha'
        | inr hb' => exact MOr.right hb'

  end exercises
end Logic

namespace Induction
  variable {α:Type}
  #print List
  /- as reminder
    inductive List.{u} : Type u → Type u
    number of parameters: 1
    constructors:
    List.nil : {α : Type u} → List α
    List.cons : {α : Type u} → α → List α → List α
  -/

  inductive Mem: α → List α → Prop where
  | mem (x tl): Mem x (x::tl)
  | cons (x hd tl) (h_rec: Mem x tl): Mem x (hd::tl)

  def mem (x: α): List α → Prop
  | [] => False
  | hd :: tl => x = hd ∨ mem x tl

  section exercices
    theorem Mem_is_mem (x:α) (l: List α): Mem x l ↔ mem x l := by
      apply Iff.intro
      · intro h; induction h with
        | mem tl => apply Or.inl; rfl;
        | cons hd tl _ ih => apply Or.inr; assumption;
      · intro h; induction l with
        | nil => contradiction;
        | cons hd tl ih => cases h with
          | inl h => subst h; apply Mem.mem;
          | inr h => apply Mem.cons; apply ih; assumption;
  end exercices

  /- Lean has its option type -/
  #print Option

  /-- Get the `i`th element of `l`, return `none` if out of bound -/
  def get (i: Nat) (l: List α): Option α := match i, l with
  | 0, hd::_ => some hd
  | Nat.succ i, _::tl => get i tl
  | _, _ => none

  theorem get_isSome_mem (i:Nat) (l:List α) (x: α) (h: get i l = some x): mem x l := by
    induction l generalizing i x with -- <- this universally quantifies `i` and `x` before calling the induction
    | nil => simp [get] at h
    | cons hd tl ih =>
      /- ih: ∀ (i : Nat) (x : α), get i tl = some x → mem x tl -/ -- we see that `i` and `x` are indeed universally quantified
      cases i with
      | zero =>
        have hx: x = hd := by cases h; rfl
        rw[hx]; left; rfl
      | succ i =>
        right
        apply ih
        apply h

  #check List.length_cons
  #check Nat.zero_lt_succ

  theorem add_lt (n m: Nat) (h: n - 1 < m) : n < m + 1 := by omega

  section exercises
    theorem get_lt_length (i:Nat) (l:List α) (x: α) (h: get i l = some x): i < l.length := by
      sorry
  end exercises

  inductive Perm: List α → List α → Prop where
  | nil : Perm [] []
  | cons (hd tl tl') (h: Perm tl tl'): Perm (hd::tl) (hd::tl')
  | swap (x y tl): Perm (x:: y:: tl) (y :: x ::tl)
  | trans (l₁ l₂ l₃) (h₁: Perm l₁ l₂) (h₂: Perm l₂ l₃): Perm l₁ l₃

  section exercices
    theorem refl (l:List α) : Perm l l := by
      induction l with
      | nil => exact Perm.nil
      | cons hd tl ih => exact Perm.cons hd tl tl ih

    theorem symm (l₁ l₂:List α) (h: Perm l₁ l₂): Perm l₂ l₁ := by
      induction h with
      | nil => apply refl
      | cons hd tl tl' _ ih => apply Perm.cons; assumption
      | swap x y tl => apply Perm.swap
      | trans l₁ l₂ l₃ _ _ ih₁ ih₂ => apply Perm.trans <;> assumption
  end exercices


  theorem Perm.length (l₁ l₂:List α) (h: Perm l₁ l₂): l₁.length = l₂.length := by
    induction h with
    | nil => rfl
    | cons hd tl tl' h ih =>
      rw[List.length_cons, List.length_cons, ih]
    | swap x y tl => repeat rw[List.length_cons]
    | trans l₁ l₂ l₃ h₁ h₂ ih₁  ih₂ => rw[ih₁, ih₂]

  -- lean is pretty good on its own and this is enough:
  example (l₁ l₂:List α) (h: Perm l₁ l₂): l₁.length = l₂.length := by
    induction h <;> simp_all

  /-
    example of a more involved proof

    This proof introduces various different tactics to more or less
    do the same thing with different levels of explicitness and automation
  -/
  theorem Perm.get (l₁ l₂: List α) (h: Perm l₁ l₂) (i: Nat):
    ∃ j:Nat, get i l₁ = get j l₂ := by
      induction h generalizing i with -- induction over the definition of `Perm`
      | nil => exists i -- introduces an `∃`, you need to explicity give the value
      | cons hd tl tl' _ ih =>
        cases i with -- we need to split on i = 0 and i ≠ 0
        | zero => exists 0
        | succ i => -- here we use the induction hypothesis `ih`
          -- have lets us introduce hypothesis in a middle of a proof
          have hi: ∃ j, Induction.get i tl = Induction.get j tl' := by
            exact ih i
          cases hi with -- <- destruct the `∃`
          | intro j hj => exists (j+1)
      | swap x y tl =>
        /- Here we split on i = 0, 1 and the rest -/
        rcases hi: i with (_ | _ | i) /- <- recursively pattern matches
          we put into `hi` the current case we are in. This is a more consise
          way of doing a similar thing as the `cases _ with` that we did in the
          `cons` case -/
        · /- i = 0 -/ exists 1
        · /- i = 1 -/ exists 0
        · /- i ≥ 2 -/ exists (i+2)
      | trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
        obtain ⟨j₁, h₁⟩:= ih₁ i
        obtain ⟨j₂, h₂⟩:= ih₂ j₁
        /- obtain is a mix of `have` and `rcases`: it introduces
          hypothesis and pattern matches on them. Now the proof is trivial -/
        exists j₂
        calc -- this lets us make proofs by transitivity. (Note that it would have be quicker to use `rw` here)
          Induction.get i l₁ = Induction.get j₁ l₂ := by assumption
          _ = Induction.get j₂ l₃ := by assumption

  section exercises
    theorem Perm.mem (l₁ l₂: List α) (h: Perm l₁ l₂) (x: α) (hx: mem x l₁): mem x l₂ := by
      sorry
  end exercises
end Induction

namespace MetaPrograming
/-
  As introduced in the extra slides of the lecture, proofs in lean are simply programs and tactics
  are macros that help us build those programs. This means that we can make proofs without tactics
  and functions with tactics
-/

  -- let's bring back the `mem` defined earlier:
  def mem (x: α): List α → Prop
  | [] => False
  | hd :: tl => x = hd ∨ mem x tl

  -- we can also define it using tactics!
  def mem': α → List α → Prop := by
    intro x l
    induction l with
    | nil => exact False
    | cons hd _ ih => exact x = hd ∨ ih
  #print mem'

  theorem mem_is_mem (x:α) (l:List α): mem x l ↔ mem' x l := by
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      constructor
      · rintro (h|h)
        · left; assumption
        · right; rw[ih] at h; assumption
      · rintro (h|h)
        · left; assumption
        · right; rwa[ih] -- <- calls `assumption` after `rw`

  /- even though we use the induction hypothesis, we can write the proof without
     the `induction` tactic -/
  theorem mem_is_mem_no_ind (x:α) (l:List α): mem x l ↔ mem' x l := by
    cases l with
    | nil => rfl
    | cons hd tl =>
      have ih: mem x tl ↔ mem' x tl := by exact mem_is_mem_no_ind x tl -- recursive call
      constructor <;> rintro (h|h)
      all_goals try (left; assumption)
      · right; rwa[ih] at h;
      · right; rwa[ih]
  /- this is due to the fact that lean builds the proof, then type checks the function.
     Thus we can make 'recursive' proofs as long as the proof 'terminate'. -/

  /- Armed with this we can actualy write the proof without tactics! -/
  theorem mem_is_mem_no_tac (x:α) (l:List α): mem x l ↔ mem' x l :=
    match l with -- the case analysis
    | List.nil => Iff.rfl
    | List.cons _ tl =>
      let ih := mem_is_mem_no_tac x tl -- the recursive call
      { mp := λ h => match h with -- the second case analysis
          | .inl h => .inl h /- `.inl` stands for `Or.inl` because leans
                                knows it expects an `Or` -/
          | .inr h => .inr (ih.mp h)
        mpr := λ h => match h with
          | .inl h => .inl h
          | .inr h => .inr (ih.mpr h) }
end MetaPrograming


/-! ## extensionality (ext) -/
section Extensionality

  def double (x : Nat) : Nat := x + x
  def double' (x : Nat) : Nat := 2 * x

  @[ext]
  theorem function_ext (f g: α → β) (h: ∀ x, f x = g x) : f = g :=
    -- this is already in `lean` as `funext` (and already tagged `ext`)
    funext h

  -- we can use the `ext` to recursively call lemmas tagged with `@[ext]`
  theorem double_eq_double' : double = double' := by
    ext x
    unfold double double'
    omega

  theorem fun_pairs {α β :Type} (f g h l: α → β)
    (h₁: ∀ x, f x = h x) (h₂: ∀ y, g y = l y) : (f, g) = (h, l) := by
    sorry

end Extensionality

/-!
## Brute force on bitvectors

The project makes use of `BitVec`tors
-/
section BitvectorExamples
  variable (n:Nat)

  /- BitVector are internally members of `ℤ/(2^n)ℤ`. However we use them as arrays of booleans -/
  #print BitVec

  /-- The `ext` tactic for `BitVec` reduce the goal to bitwise operations -/
  theorem and_refl (a :BitVec n) : a &&& a = a := by
    ext i hi
    rw[BitVec.getElem_and]
    cases a[i] <;> rfl

  -- We have ac computer, so we can go faster !
  theorem brute_force (k:Nat) (a b c: BitVec n):
    (a <<< k) ^^^ (b <<< k) ^^^ (c <<< (2*k)) = (a ^^^ b ^^^ (c <<< k)) <<< k := by
    ext i hi
    have: c[i - k - k] =  c[i - 2 * k] := by apply getElem_congr; rfl; omega
    simp only [this, BitVec.getElem_xor, BitVec.getElem_shiftLeft]; clear this

    -- we brute force our way on all the boolean in the expressions
    cases h₁: decide (i < k) <;> cases h₂: decide (i < 2 * k) <;> cases h₃: decide (i - k < k)
      <;> (simp only [decide_eq_false_iff_not, decide_eq_true_eq] at *) -- get rid of the `decides`
      <;> cases a[i - k] <;> cases b[i - k]
      <;> cases c[i - 2 * k]
      <;> try rfl
    -- the rest are contradictions
    all_goals exfalso
    all_goals omega

  theorem brute_force' (k:Nat) (a b c: BitVec n):
    (a <<< k) ^^^ (b <<< k) ^^^ (c <<< (2*k)) = (a ^^^ b ^^^ (c <<< k)) <<< k := by
    ext i hi
    -- lean has powerful tactics that can let us to this automagically
    grind -- <- a staturation + equality "solver" within lean.
          -- Beware, it can be quite fragile and it isn't designed for too heavy cases analysis (it can timeout)
          -- it also imports the dreaded `Classical`
end BitvectorExamples
