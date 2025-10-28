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
#check refl
#check irrefl
#check antisymm
#check trans
#check total_of
end Orderings


-- ===================================================
-- Mostly ASR, with some elements from Orderings
-- ===================================================
section ExerciseSheet1

open ASR

inductive ASR_Counter

end ExerciseSheet1

-- -- inverse does not hold
-- -- A concrete 3-element counterexample showing that
-- -- normalizing does NOT imply terminating in general.
-- -- We'll build a type with three elements and a relation that loops (infinite chain)
-- -- but still has a normal form reachable from every element.

-- namespace Counterexample

-- -- a simple 3-element type
-- inductive Three where
-- | a | b | c
-- deriving DecidableEq

-- open Three

-- -- relation with a 2-cycle a ↔ b and edges to a normal form c
-- -- a → b, b → a, a → c, b → c, and c has no outgoing edges
-- def r3 : Set (Three × Three) :=
--   { p | p = (Three.a, Three.b) ∨ p = (Three.b, Three.a) ∨ p = (Three.a, Three.c) ∨ p = (Three.b, Three.c) }

-- -- Handy facts for simp
-- lemma r3_ab : (Three.a, Three.b) ∈ r3 := by simp [r3]
-- lemma r3_ba : (Three.b, Three.a) ∈ r3 := by simp [r3]
-- lemma r3_ac : (Three.a, Three.c) ∈ r3 := by simp [r3]
-- lemma r3_bc : (Three.b, Three.c) ∈ r3 := by simp [r3]

-- -- c is irreducible in r3
-- lemma r3_irreducible_c : asr_irreducible r3 Three.c := by
--   -- asr_irreducible r3 c ≡ ¬ ∃ y, (c, y) ∈ r3
--   unfold asr_irreducible asr_reducible
--   -- no pair in r3 starts with c
--   simp [r3]

-- -- show that every element reaches c (a normal form) in ≤ 1 step
-- lemma r3_reaches_c : ∀ x : Three, (x, Three.c) ∈ asr_reflexive_transitive_closure r3 := by
--   intro x
--   cases x with
--   | a =>
--     -- a → c in one step
--     unfold asr_reflexive_transitive_closure
--     refine Set.mem_iUnion.mpr ?_
--     refine ⟨1, ?_⟩
--     -- build a membership in comp (id) r3 and rewrite by definition of power 1
--     have hx0 : (Three.a, Three.a) ∈ asr_power 0 r3 := by simp [asr_power]
--     have hcomp : (Three.a, Three.c) ∈ comp (asr_power 0 r3) r3 := ⟨Three.a, hx0, r3_ac⟩
--     simpa [asr_power] using hcomp
--   | b =>
--       -- b → c in one step
--       unfold asr_reflexive_transitive_closure
--       refine Set.mem_iUnion.mpr ?_
--       refine ⟨1, ?_⟩
--     have hx0 : (Three.b, Three.b) ∈ asr_power 0 r3 := by simp [asr_power]
--     have hcomp : (Three.b, Three.c) ∈ comp (asr_power 0 r3) r3 := ⟨Three.b, hx0, r3_bc⟩
--     simpa [asr_power] using hcomp
--   | c =>
--       -- reflexivity: (c, c) in power 0
--       unfold asr_reflexive_transitive_closure
--       refine Set.mem_iUnion.mpr ?_
--     exact ⟨0, by simp [asr_power]⟩

-- -- r3 is normalizing: every element can reach c, and c is irreducible
-- lemma r3_normalizing : asr_normalizing r3 := by
--   intro x
--   refine ⟨Three.c, ?_⟩
--   -- asr_is_normalform_of r3 c x ≡ (x, c) ∈ rtc(r3) ∧ irreducible c
--   exact ⟨r3_reaches_c x, r3_irreducible_c⟩

-- -- a simple toggle and alternating sequence: a, b, a, b, ...
-- def toggle : Three → Three
-- | Three.a => Three.b
-- | Three.b => Three.a
-- | Three.c => Three.a

-- def alt : ℕ → Three
-- | 0 => Three.a
-- | n+1 => toggle (alt n)

-- lemma toggle_ne_c (x : Three) : toggle x ≠ Three.c := by
--   cases x <;> simp [toggle]

-- lemma alt_ne_c : ∀ n, alt n ≠ Three.c := by
--   intro n; induction n with
--   | zero => simp [alt]
--   | succ n ih =>
--       -- alt (n+1) = toggle (alt n), and toggle never returns c
--       simpa [alt] using toggle_ne_c (alt n)

-- lemma alt_is_a_or_b : ∀ n, alt n = Three.a ∨ alt n = Three.b := by
--   intro n; induction n with
--   | zero => simp [alt]
--   | succ n ih =>
--       rcases ih with h | h
--       · simp [alt, toggle, h]
--       · simp [alt, toggle, h]

-- lemma alt_step_in_r3 (n : ℕ) : (alt n, alt (n + 1)) ∈ r3 := by
--   -- decide on whether alt n is a or b
--   rcases alt_is_a_or_b n with h | h
--   · -- alt n = a ⇒ next is b
--     have : alt (n + 1) = Three.b := by simp [alt, toggle, h]
--     simpa [h, this] using r3_ab
--   · -- alt n = b ⇒ next is a
--     have : alt (n + 1) = Three.a := by simp [alt, toggle, h]
--     simpa [h, this] using r3_ba

-- -- r3 is not terminating: the function `alt` witnesses an infinite chain
-- lemma r3_not_terminating : ¬ asr_terminating r3 := by
--   intro hterm
--   -- build the infinite chain with `alt`
--   have hChain : ∀ n : ℕ, (alt n, alt (n + 1)) ∈ r3 := by
--     intro n; exact alt_step_in_r3 n
--   exact hterm ⟨alt, hChain⟩

-- end Counterexample

-- open Counterexample

-- -- Final statement: there exists a normalizing but non-terminating relation
-- -- hence, it's not true in general that normalizing implies terminating.
-- -- A concrete existential counterexample: normalizing but not terminating
-- -- A concrete counterexample on a 3-element type
-- example : asr_normalizing Counterexample.r3 := Counterexample.r3_normalizing
-- example : ¬ asr_terminating Counterexample.r3 := Counterexample.r3_not_terminating


 -- intro x hx
  -- by_contra hno
  -- -- hno : ¬ ∃ y, (x, y) ∈ r
  -- have hx_irred : asr_irreducible r x := by
  --   -- asr_irreducible r x := ¬ asr_reducible r x, and asr_reducible r x := ∃ c, (x, c) ∈ r
  --   unfold asr_irreducible asr_reducible
  --   simpa using hno
  -- have hx_norm : asr_is_normalform_of r x b := by
  --   unfold asr_is_normalform_of
  --   exact ⟨hx, hx_irred⟩
  -- exact h ⟨x, hx_norm⟩
