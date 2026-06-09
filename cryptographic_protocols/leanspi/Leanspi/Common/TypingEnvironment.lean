import Mathlib.Tactic
import Mathlib.Data.Prod.Basic

variable {α β : Type} [DecidableEq α]

-- A typing environment is a list of pairs

def TypingEnvironment α β := List (α × β)

namespace TypingEnvironment

-- We can get an element using the List.find? function
abbrev get g v := Prod.snd <$> List.find? (fun (x : (α × β)) => (Prod.fst x) = v) g

instance : EmptyCollection (TypingEnvironment α β) := ⟨[]⟩
instance : Membership α (TypingEnvironment α β) := ⟨λ g v => (get g v).isSome ⟩
instance : HAppend (TypingEnvironment α β) (α × β) (TypingEnvironment α β) := ⟨λ Γ t => List.cons t Γ⟩

-- GetElem? implements the []? sintax for getting elements
instance : GetElem? (TypingEnvironment α β) α β λ g v => v ∈ g where
  getElem? := get
  getElem g v h := (get g v).get (by simp_all[Membership.mem,get])

-- The domain of a typing environment is the list of keys
@[simp]
def dom : TypingEnvironment α β -> List α
| [] => ∅
| (a, _) :: tl => a :: dom tl

-- The rest of the file defines useful lemmas that describing the typing environment

@[simp] def get_reduce (g : TypingEnvironment α β) (n m : α) (t : β) : (m ≠ n) -> (g ++ (n, t))[m]? = g[m]? := by
  intro ne
  simp_all[HAppend.hAppend,GetElem?.getElem?,get]
  rw[List.find?_cons_of_neg]; simp; intro a; exact ne (Eq.symm a)

@[simp] def get_append (g : TypingEnvironment α β) (n : α) (t : β) : (g ++ (n, t))[n]? = some t := by
  simp_all[HAppend.hAppend,GetElem?.getElem?,get]

@[simp] def getElem?_emptyc {a : @α} : (∅ : @TypingEnvironment α β)[a]? = (none : Option (β)) := by
  simp_all[HAppend.hAppend,GetElem?.getElem?,EmptyCollection.emptyCollection,get]

lemma get_append_comm (g : TypingEnvironment α β) (n n' m : α) (t t' : β) (h: n ≠ n') :
 (g ++ (n, t) ++ (n', t'))[m]? = (g ++ (n', t') ++ (n, t))[m]? := by
   by_cases hn: (m = n) <;> by_cases hn': (m = n') <;> (try (first| subst hn hn' | subst hn | subst hn')) <;>
   simp_all only [ne_eq, not_false_eq_true, get_append, get_reduce]
   contradiction

lemma get_none_mem_not {Γ : TypingEnvironment α β} {M: α} : (M ∉ Γ) <-> (Γ[M]? = none) := by
  simp [Membership.mem, GetElem?.getElem?,get]
  aesop

lemma get_some_mem {Γ : TypingEnvironment α β} {M: α} : (M ∈ Γ) <-> (∃ T, Γ[M]? = some T) := by
  simp [Membership.mem,GetElem?.getElem?,get,-List.find?_isSome]
  constructor <;>  rw[Option.isSome_iff_exists]
  rintro ⟨⟨M,T⟩, h⟩; simp_all
  rintro ⟨T, A, h⟩; simp_all

omit [DecidableEq α] in
@[simp]
lemma empty_insert_ne (Γ : TypingEnvironment α β) (M: α) (T: β) : ∅ ≠ (Γ ++ (M,T)) := by
  simp [HAppend.hAppend, EmptyCollection.emptyCollection]

lemma nin_append_ne {Γ : TypingEnvironment α β} {M: α} {T: β} (h: A ∉ (Γ ++ (M, T))) : A ≠ M := by
  simp [HAppend.hAppend, Membership.mem, get] at h
  intro eq; subst A; apply h T (List.Mem.head _)

lemma nin_append_rec {Γ : TypingEnvironment α β} {M: α} {T: β} (h: A ∉ (Γ ++ (M, T))) : A ∉ Γ := by
  simp_all [HAppend.hAppend, Membership.mem,get]
  intro x; specialize h x
  intro hin; apply h (List.Mem.tail _ hin)

lemma in_append_or {Γ : TypingEnvironment α β} {M: α} {T: β} (h: A ∈ (Γ ++ (M, T))) : A ∈ Γ ∨ A = M := by
  simp_all [HAppend.hAppend, Membership.mem,get]
  obtain ⟨T, h⟩ := h
  cases h <;> tauto

lemma in_append_or' {Γ : TypingEnvironment α β} {M: α} {T: β} (h: A ∈ (Γ ++ (M, T))) : (A ∈ Γ ∧ A ≠ M) ∨ A = M := by
  simp_all [HAppend.hAppend, Membership.mem,get]
  obtain ⟨T, h⟩ := h
  cases h <;> tauto

lemma or_append_in {Γ : TypingEnvironment α β} {M: α} {T: β} (h: A ∈ Γ ∨ A = M) : A ∈ (Γ ++ (M, T)) := by
  simp_all [HAppend.hAppend, Membership.mem,get]
  cases h; tauto; subst A; tauto

lemma dom_perm : List.Perm Γ Γ' -> List.Perm (dom Γ) (dom Γ') := by
  intro p
  induction p <;> try simp_all
  tauto; constructor <;> assumption

lemma get_perm_nodup {Γ Γ' : TypingEnvironment α β} {M: α} (h: List.Perm Γ Γ') (h': Γ.dom.Nodup) : Γ[M]? = Γ'[M]? := by
  have append_cons : ∀ (x : (α × β)) (l: TypingEnvironment α β), (x :: l) = (l ++ x) := by simp[HAppend.hAppend]
  induction h with
  | nil => rfl
  | cons x  p₁ ih =>
    simp_all[append_cons]
    by_cases h: x.1 = M
    have : (x.1,x.2) = x := by simp
    rw[<-this, h]
    simp[get_append]
    rw[get_reduce, get_reduce]
    assumption
    all_goals exact fun a => h (Eq.symm a)
  | swap x y l =>
    simp_all[append_cons]
    by_cases x.1 = M
    · rw[get_reduce]
      have : (x.1,x.2) = x := by {simp}; rw[<-this]; subst M; rw[get_append,get_append]; simp_all; tauto
    · rewrite (config := {occs := .pos [2]}) [get_reduce]
      by_cases y.1 = M
      · subst M
        have : (y.1,y.2) = y := by {simp}; rw[<-this, get_append,get_append]
      · rw [get_reduce,get_reduce,get_reduce] <;> tauto
      · tauto
  | trans l₁ _ ih ih₁ =>
    rw[ ih h']; apply ih₁
    have := dom_perm l₁
    exact List.Perm.nodup this h'

omit [DecidableEq α] in
lemma append_perm {Γ : TypingEnvironment α β} {M A: α} {T B: β} : List.Perm (Γ ++ (A, B) ++ (M, T)) (Γ ++ (M, T) ++ (A, B)) :=  by
  simp[HAppend.hAppend]; tauto

end TypingEnvironment
