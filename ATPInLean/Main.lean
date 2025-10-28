
import Mathlib.Data.Set.Basic

-- big Union
import Mathlib.Data.Set.Lattice

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

-- abstract reduction system
variable {A : Type*} [Nonempty A]

-- composition of relations given as sets of pairs
-- (a, c) ∈ comp r r' iff ∃ b, (a, b) ∈ r ∧ (b, c) ∈ r'
def comp (r r' : Set (A × A)) : Set (A × A) :=
  { p | ∃ b, (p.1, b) ∈ r ∧ (b, p.2) ∈ r' }

-- n-fold composition power of a relation r; 0 gives the identity relation
def asr_power : ℕ → Set (A × A) → Set (A × A)
| 0, _ => { p | p.1 = p.2 }
| n+1, r => comp (asr_power n r) r

def asr_identity : Set (A × A) → Set (A × A) := asr_power 0

-- Reuse a fixed relation `r` across the following defs using a section-scoped variable.
section
variable (r : Set (A × A))

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

-- Variant restricted to a subset S ⊆ A
def asr_normalizing_on (S : Set A) : Prop :=
  ∀ ⦃b : A⦄, b ∈ S → ∃ c : A, c ∈ S ∧ asr_is_normalform_of r c b

end



-- Exercise Sheet 1 =========




-- end ======================
