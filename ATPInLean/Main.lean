import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice -- big Union


-- ===================================================
-- Using mathlib, mostly
-- ===================================================
namespace MathematicalPrerequisites

-- explicit demonstrating that 0 ∈ ℕ
example : 0 ∈ (Set.univ : Set ℕ) := by
  simp

variable {α : Type*} {M M' : Set α} {a b : α }

-- make sure that notations work
example : M ⊂ M' ↔ M ⊆ M' ∧ M ≠ M' := by
  exact Set.ssubset_iff_subset_ne

-- cartesian product with ×ˢ
example : a ∈ M ∧ b ∈ M → (a, b) ∈ (M ×ˢ M) := by
  intro ⟨ ma, mb ⟩
  exact Set.mk_mem_prod ma mb

-- omitted: n-fold cartesian product built from ×ˢ
-- if this flexibility is needed, use Fin n probably

-- mini example with relations
def R : Set (ℕ × ℕ) := {p |
    p = (0, 2) ∨
    p = (1, 2) ∨
    p = (2, 2) ∨
    p = (3, 2)
  }

def R' : Set (ℕ × ℕ) := {p |
    p = (0, 2) ∨
    p = (1, 2)
}

example : R ∩ {p | p.1 < p.2} = R' := by
  ext p
  constructor
  · intro ⟨ hR, hLt ⟩
    rw [R']
    simp
    rw [R] at hR
    simp at hR
    rcases hR with h | h | h | h
    · left; exact h
    · right; exact h
    · exfalso
      simp at hLt
      rw [h] at hLt
      simp at hLt -- hä? why is this working?
      -- why is it displayed this way?
      -- ah, simp is clever
    · exfalso
      simp at hLt
      rw [h] at hLt
      simp at hLt
  · intro h
    constructor
    rw [R'] at h
    simp at h
    · rw [R]
      simp
      rcases h with h | h
      · left; exact h
      · right; left; exact h
    · simp
      rw [R'] at h
      simp at h
      rcases h with h | h
      · rw [h]
        simp
      · rw [h]
        simp

-- use List for words
-- operate on Sets for mathematical notation
def Sig (α : Type*) : Set α := Set.univ
def SigStar (α : Type*) : Set (List α) := Set.univ
def epsilon (α : Type*) : List α := []

example : epsilon α ∈ SigStar α := by
  rw [SigStar, epsilon]
  simp

example (u : List α) (a : α) : u ∈ SigStar α ∧ a ∈ Sig α → (u ++ [a]) ∈ SigStar α := by
  intro _
  rw [SigStar]
  simp

example : (epsilon α).length = 0 := by
  rw [epsilon]
  simp

example (u : List α) (a : α) : u ∈ SigStar α → a ∈ Sig α → (u ++ [a]).length = u.length + 1 := by
  simp

end MathematicalPrerequisites




-- ===================================================
-- Abstract Reduction Systems and properties
-- ===================================================
namespace ARS

variable {A : Type*}
variable (r : Set (A × A))

-- composition of relations given as sets of pairs
-- (a, c) ∈ comp r r' iff ∃ b, (a, b) ∈ r ∧ (b, c) ∈ r'
def comp (r r' : Set (A × A)) : Set (A × A) :=
  { p | ∃ b, (p.1, b) ∈ r ∧ (b, p.2) ∈ r' }

-- n-fold composition power of a relation r; 0 gives the identity relation
def asr_power : ℕ → Set (A × A) → Set (A × A)
| 0, _ => { p | p.1 = p.2 }
| n+1, r => comp (asr_power n r) r

def asr_identity : Set (A × A) → Set (A × A) := asr_power 0

def asr_transitive_closure : Set (A × A) :=
  ⋃ n : ℕ, asr_power (n + 1) r

def asr_reflexive_transitive_closure : Set (A × A) :=
  ⋃ n : ℕ, asr_power n r

def asr_reflexive_closure : Set (A × A) :=
  asr_identity r ∪ asr_power 1 r

def asr_inverse : Set (A × A) :=
  { p | r (p.2, p.1) }

def asr_symmetric_closure : Set (A × A) :=
  r ∪ asr_inverse r

def asr_transitive_symmetric_closure : Set (A × A) :=
  asr_transitive_closure (asr_symmetric_closure r)

def asr_equivalence_closure : Set (A × A) :=
  asr_reflexive_transitive_closure (asr_symmetric_closure r)

-- An element b is reducible if it relates to some c via r
def asr_reducible (b : A) := ∃ c : A, (b, c) ∈ r

def asr_irreducible (b: A) := ¬ asr_reducible r b

def asr_is_normalform_of (c: A) (b: A) :=
  (b, c) ∈ asr_reflexive_transitive_closure r ∧ asr_irreducible r c

-- A relation is terminating if there is no infinite chain b₀ → b₁ → b₂ → ···
def asr_terminating :=
  ¬ ∃ f : ℕ → A, ∀ n : ℕ, (f n, f (n + 1)) ∈ r

-- Normalizing means every element has a normal form reachable via r
def asr_normalizing : Prop := ∀ b : A, ∃ c : A, asr_is_normalform_of r c b

lemma aux_exists_next_of_not_normalizing
  (r : Set (A × A)) (b : A)
  (h : ¬ ∃ c : A, asr_is_normalform_of r c b) :
  ∀ x : A, (b, x)
    ∈ asr_reflexive_transitive_closure r → ∃ y : A, (x, y) ∈ r := by
  intro x hrtc
  rw [not_exists] at h
  specialize h x
  rw [asr_is_normalform_of, not_and_or] at h
  rcases h with h | h
  · contradiction
  · rw [asr_irreducible, Classical.not_not, asr_reducible] at h
    exact h

lemma aux_exists_infinity_chain_of_not_normalizing
  (r : Set (A × A)) :
  ¬ asr_normalizing r → ∃ f : ℕ → A, ∀ n : ℕ, (f n, f (n + 1)) ∈ r := by
  intro not_nor
  rw [asr_normalizing, not_forall] at not_nor
  obtain ⟨ b, hb ⟩ := not_nor

  -- subtypes are a bit spooky
  let Reachable := {x : A // (b, x) ∈ asr_reflexive_transitive_closure r }

  have reachable_next
    (x : Reachable) :
    ∃ y : Reachable, (x.val, y.val) ∈ r := by
    have xp := x.property
    have hnext := aux_exists_next_of_not_normalizing r b hb x xp
    obtain ⟨ y', h ⟩ := hnext
    have prop :  (b, y') ∈ asr_reflexive_transitive_closure r := by
      rw [asr_reflexive_transitive_closure]
      unfold asr_reflexive_transitive_closure at xp
      -- these two lines are tricky
      rcases Set.mem_iUnion.mp xp with ⟨ n, hxN ⟩
      refine Set.mem_iUnion.mpr ?_
      use n + 1
      rw [asr_power, comp]
      simp
      use x
    use ⟨ y', prop ⟩

  let f : ℕ → Reachable := Nat.rec
    ⟨ b, (by
      rw [asr_reflexive_transitive_closure]
      simp
      use 0
      rw [asr_power]
      simp
    )⟩
    (fun _ x => Classical.choose (reachable_next x))

  let f_loose : ℕ → A := fun n => (f n).val
  use f_loose
  intro n

  -- crazy, that this works in such a compact form
  exact Classical.choose_spec (reachable_next (f n))

lemma asr_terminating_normalizing (r: Set (A × A)) :
  asr_terminating r → asr_normalizing r := by
  intro ht
  by_contra not_nor
  have chain := aux_exists_infinity_chain_of_not_normalizing r not_nor
  contradiction

end ARS


-- ===================================================
-- More definitions, reusing from matlib if possible
-- ===================================================
namespace Orderings
-- #check refl
-- #check irrefl
-- #check antisymm
-- #check trans
-- #check total_of
end Orderings


-- ===================================================
-- Mostly ASR, with some elements from Orderings
-- ===================================================
section ExerciseSheet1

open ARS

-- Exercise 1.3 simplified version for counterexample noted in script
inductive X where
| e1 | e2 | e3

open X

def R : Set (X × X) :=
  { p | p = (e1, e2) ∨ p = (e2, e1) ∨ p = (e1, e3) ∨ p = (e2, e3)}

lemma R_e1e2 : (e1, e2) ∈ R := by simp [R]
lemma R_e2e1 : (e2, e1) ∈ R := by simp [R]
lemma R_e1e3 : (e1, e3) ∈ R := by simp [R]
lemma R_e2e3 : (e2, e3) ∈ R := by simp [R]

lemma e3_irreducible : asr_irreducible R e3 := by
  unfold asr_irreducible asr_reducible
  simp [R]

lemma e3_normal_of_e3 : asr_is_normalform_of R e3 e3 := by
  unfold asr_is_normalform_of
  constructor
  · unfold asr_reflexive_transitive_closure
    simp; use 0; simp [asr_power]
  · exact e3_irreducible

lemma e3_normal_of_e1 : asr_is_normalform_of R e3 e1 := by
  unfold asr_is_normalform_of
  constructor
  · unfold asr_reflexive_transitive_closure
    simp; use 1; unfold asr_power asr_power comp; simp [R]
  · exact e3_irreducible

lemma e3_normal_of_e2 : asr_is_normalform_of R e3 e2 := by
  unfold asr_is_normalform_of
  constructor
  · unfold asr_reflexive_transitive_closure
    simp; use 1; unfold asr_power asr_power comp; simp [R]
  · exact e3_irreducible

lemma R_normalizing: asr_normalizing R := by
  unfold asr_normalizing
  intro x
  rcases x with e1 | e2 | e3
  · use e3
    exact e3_normal_of_e1
  · use e3
    exact e3_normal_of_e2
  · use e3
    exact e3_normal_of_e3

def toggle : X → X
| e1 => e2
| e2 => e1
| e3 => e1 -- placeholder

def alt : ℕ → X
| 0 => e1
| n+1 => toggle (alt n)

lemma alt_never_e3 : ∀ n : ℕ, alt n ≠ e3 := by
  intro n
  induction n with
  | zero => simp [alt]
  | succ n ih =>
    simp [alt]
    rcases alt n with e1 | e2 | e3 <;> simp [toggle]

lemma Counterexample : asr_normalizing R ∧  ¬asr_terminating R := by
  rw [and_iff_not_or_not]
  intro h
  rcases h with h | h
  · apply h
    exact R_normalizing
  · have h' : ¬ asr_terminating R := by
      unfold asr_terminating
      rw [not_not]
      use alt
      intro n
      rw [alt]
      have e1_or_e2 : alt n = e1 ∨ alt n = e2 := by
        rcases h: alt n with e1 | e2 | e3
        · simp
        · simp
        · exfalso
          exact (alt_never_e3 n h)
      rcases e1_or_e2 with e1 | e2
      · rw [e1]
        simp [toggle, R]
      · rw [e2, toggle]
        simp [R]
    contradiction

-- Exercise 1.2
inductive Y where
| y1 | y2

open Y

def S : Set (Y × Y) :=
  {p | p = (y1, y2)}

def S' := asr_symmetric_closure S

def S'' := asr_equivalence_closure S

-- TODO: this proof is completely over the top
example : S ≠ S' ∧ S ≠ S'' ∧ S' ≠ S'' := by
  -- S ≠ S'
  constructor
  · intro h
    have hyS' : (y2, y1) ∈ S' := by
      simp [S', asr_symmetric_closure]
      right
      unfold asr_inverse S
      exact rfl -- kinda weird
    have hyNotS : (y2, y1) ∉ S := by
      simp [S]
    rw [h] at hyNotS
    contradiction
  -- S ≠ S''
  constructor
  · intro h
    have hyyS'' : (y1, y1) ∈ S'' := by
      unfold S'' asr_equivalence_closure asr_reflexive_transitive_closure
      simp; use 0; simp [asr_power]
    have hyyNotS : (y1, y1) ∉ S := by
      simp [S]
    rw [h] at hyyNotS
    contradiction
  -- S' ≠ S''
  · intro h
    have hyyS'' : (y1, y1) ∈ S'' := by
      unfold S'' asr_equivalence_closure asr_reflexive_transitive_closure
      simp; use 0; simp [asr_power]
    have hyyNotS' : (y1, y1) ∉ S' := by
      unfold S' asr_symmetric_closure
      simp
      constructor
      · simp [S]
      · unfold asr_inverse; simp;
        intro h
        unfold S at h
        simp at h
        have t : y1 ≠ y2 := by simp
        have t': (y1, y1) = (y1, y2) := by -- this is weird
          apply h;
        have t'': y1 = y2 := by
          rw [Prod.mk.injEq] at t' -- some magic
          exact t'.2
        contradiction
    rw [h] at hyyNotS'
    contradiction

end ExerciseSheet1
