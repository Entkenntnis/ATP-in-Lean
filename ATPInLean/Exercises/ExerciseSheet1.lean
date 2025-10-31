import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Prime.Basic
import ATPInLean.Sections.«02_AbstractReductionSystem»

import Mathlib.Tactic

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

lemma e3_irreducible : ars_irreducible R e3 := by
  unfold ars_irreducible ars_reducible
  simp [R]

lemma e3_normal_of_e3 : ars_is_normalform_of R e3 e3 := by
  unfold ars_is_normalform_of
  constructor
  · unfold ars_reflexive_transitive_closure
    simp; use 0; simp [ars_power]
  · exact e3_irreducible

lemma e3_normal_of_e1 : ars_is_normalform_of R e3 e1 := by
  unfold ars_is_normalform_of
  constructor
  · unfold ars_reflexive_transitive_closure
    simp; use 1; unfold ars_power ars_power comp; simp [R]
  · exact e3_irreducible

lemma e3_normal_of_e2 : ars_is_normalform_of R e3 e2 := by
  unfold ars_is_normalform_of
  constructor
  · unfold ars_reflexive_transitive_closure
    simp; use 1; unfold ars_power ars_power comp; simp [R]
  · exact e3_irreducible

lemma R_normalizing: ars_normalizing R := by
  unfold ars_normalizing
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

lemma Counterexample : ars_normalizing R ∧  ¬ars_terminating R := by
  rw [and_iff_not_or_not]
  intro h
  rcases h with h | h
  · apply h
    exact R_normalizing
  · have h' : ¬ ars_terminating R := by
      unfold ars_terminating
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

def S' := ars_symmetric_closure S

def S'' := ars_equivalence_closure S

example : S ≠ S' ∧ S ≠ S'' ∧ S' ≠ S'' := by
  -- S ≠ S'
  constructor
  · intro h
    have hyS' : (y2, y1) ∈ S' := by
      simp [S', ars_symmetric_closure]
      right
      unfold ars_inverse S
      exact rfl -- kinda weird
    have hyNotS : (y2, y1) ∉ S := by
      simp [S]
    rw [h] at hyNotS
    contradiction
  -- S ≠ S''
  constructor
  · intro h
    have hyyS'' : (y1, y1) ∈ S'' := by
      unfold S'' ars_equivalence_closure ars_reflexive_transitive_closure
      simp; use 0; simp [ars_power]
    have hyyNotS : (y1, y1) ∉ S := by
      simp [S]
    rw [h] at hyyNotS
    contradiction
  -- S' ≠ S''
  · intro h
    have hyyS'' : (y1, y1) ∈ S'' := by
      unfold S'' ars_equivalence_closure ars_reflexive_transitive_closure
      simp; use 0; simp [ars_power]
    have hyyNotS' : (y1, y1) ∉ S' := by
      unfold S' ars_symmetric_closure
      simp
      constructor
      · simp [S]
      · unfold ars_inverse; simp;
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


-- Exercise 1.4
--  Let (N \ {0, 1}, <_d) be the set of natural numbers larger than 1 ordered
--  by the divisibility ordering <_d that is defined by a <_d b if a divides b and a ≠ b. Are
--  there minimal elements? Is there a smallest element? What do they look like?

def ltDvd (a b : ℕ) := a ∣ b ∧ a ≠ b

def minimal (a : ℕ) : Prop := ¬ ∃ b : ℕ, 1 < b ∧ ltDvd b a

lemma two_minimal: minimal 2 := by
  unfold minimal
  intro ⟨ x , hx ⟩
  unfold ltDvd at hx
  obtain ⟨ a, b, c ⟩ := hx
  apply c
  apply Nat.le_of_dvd at b <;> linarith

lemma no_smallest : ¬ ∃ s : ℕ, 1 < s ∧ ∀ x : ℕ, 1 < x → s ∣ x := by
  intro ⟨ e, ⟨ he, h ⟩ ⟩
  specialize h (e + 1)
  simp at h
  grind

lemma minimal_iff_prime (a : ℕ) (ha: 1 < a) : minimal a  ↔ Nat.Prime a := by
  sorry


-- Exercise 1.5 would be nice, too


end ExerciseSheet1
