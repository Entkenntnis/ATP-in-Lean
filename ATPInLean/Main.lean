
import Mathlib.Data.Set.Basic

-- explicit demonstrating that 0 ∈ ℕ
example : 0 ∈ (Set.univ : Set ℕ) := by
  simp


variable {α : Type*} {M M' : Set α}

-- make sure that notations work
example : M ⊂ M' ↔ M ⊆ M' ∧ M ≠ M' := by
  exact Set.ssubset_iff_subset_ne

-- TODO cartesion product ???
-- example : a ∈ M ∧ b ∈ M → (a, b) ∈ (M × M) := by
--   sorry
