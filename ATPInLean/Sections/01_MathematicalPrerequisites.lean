import Mathlib.Data.Set.Basic

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
