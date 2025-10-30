import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice -- big Union

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
def ars_power : ℕ → Set (A × A) → Set (A × A)
| 0, _ => { p | p.1 = p.2 }
| n+1, r => comp (ars_power n r) r

def ars_identity : Set (A × A) → Set (A × A) := ars_power 0

def ars_transitive_closure : Set (A × A) :=
  ⋃ n : ℕ, ars_power (n + 1) r

lemma ars_transitive_closure_trans (a b c: A) :
  (a, b) ∈ (ars_transitive_closure r) → (b, c) ∈ (ars_transitive_closure r) →
  (a, c) ∈ (ars_transitive_closure r) := by
  unfold ars_transitive_closure
  intro hab hbc
  -- Unfold the unions to obtain concrete path lengths n and m
  rcases Set.mem_iUnion.mp hab with ⟨n, h_ab⟩
  rcases Set.mem_iUnion.mp hbc with ⟨m, h_bc⟩
  -- Compose a length-(n+1) path a→b with a length-(m+1) path b→c
  have compose_len : ∀ (m : ℕ), ∀ c, (b, c) ∈ ars_power (m + 1) r → (a, c) ∈ ars_power (n + m + 2) r := Nat.rec
    (by
      simp
      intro c hbc
      rw [ars_power] at hbc
      rw [ars_power] at hbc
      unfold comp at hbc
      simp at hbc
      unfold ars_power comp
      simp
      use b
    )
    (by
      -- quite a lot of magic is happening in the last intro
      -- it can look through a lot of definitions and arrive at the ∃ in comp in ars_power
      intro m ih c ⟨ x, hx ⟩
      unfold ars_power comp
      simp
      use x
      constructor
      · apply ih
        exact hx.left
      · exact hx.right
    )
  -- Package the concrete path length back into the union
  refine Set.mem_iUnion.mpr ?_
  refine ⟨n + m + 1, ?_⟩
  exact compose_len m c h_bc

-- "real" number of hops is len + 1, so no empty paths
lemma ars_path_function_between_two_transitive_elements :
  ∀ len : ℕ,
    ∀ a b : A,
      (a, b) ∈ ars_power len r →
        ∃ g : ℕ → A,
          g 0 = a ∧ g len = b ∧
          (∀ i, i < len → (g i, g (i + 1)) ∈ r) := by
  intro len
  induction len with
  | zero =>
      simp
      intro a b hab
      unfold ars_power at hab
      simp at hab
      rw [hab]
      simp
      use fun _ => b
  | succ len ih =>
      intro a b hab
      unfold ars_power comp at hab
      simp at hab
      obtain ⟨ b', ⟨ hb₁, hb₂ ⟩ ⟩ := hab
      specialize ih a b' hb₁
      obtain ⟨ g, ⟨ hg1, hg2, hg3 ⟩ ⟩ := ih
      refine ⟨fun n => if n < len + 1 then g n else b, ?_ ⟩
      -- grind can complete the rest from here
      simp
      constructor
      · exact hg1
      · intro i hi
        by_cases hcase : i < len
        · simp [hcase]
          simp [hi]
          specialize hg3 i
          apply hg3
          exact hcase
        · have hi' : i = len := by
            exact Nat.eq_of_lt_succ_of_not_lt hi hcase
          simp [hi']
          rw [hg2]
          exact hb₂


def ars_reflexive_transitive_closure : Set (A × A) :=
  ⋃ n : ℕ, ars_power n r

def ars_reflexive_closure : Set (A × A) :=
  ars_identity r ∪ ars_power 1 r

def ars_inverse : Set (A × A) :=
  { p | r (p.2, p.1) }

def ars_symmetric_closure : Set (A × A) :=
  r ∪ ars_inverse r

def ars_transitive_symmetric_closure : Set (A × A) :=
  ars_transitive_closure (ars_symmetric_closure r)

def ars_equivalence_closure : Set (A × A) :=
  ars_reflexive_transitive_closure (ars_symmetric_closure r)

-- An element b is reducible if it relates to some c via r
def ars_reducible (b : A) := ∃ c : A, (b, c) ∈ r

def ars_irreducible (b: A) := ¬ ars_reducible r b

def ars_is_normalform_of (c: A) (b: A) :=
  (b, c) ∈ ars_reflexive_transitive_closure r ∧ ars_irreducible r c

-- A relation is terminating if there is no infinite chain b₀ → b₁ → b₂ → ···
def ars_terminating :=
  ¬ ∃ f : ℕ → A, ∀ n : ℕ, (f n, f (n + 1)) ∈ r

-- Normalizing means every element has a normal form reachable via r
def ars_normalizing : Prop := ∀ b : A, ∃ c : A, ars_is_normalform_of r c b

lemma aux_exists_next_of_not_normalizing
  (r : Set (A × A)) (b : A)
  (h : ¬ ∃ c : A, ars_is_normalform_of r c b) :
  ∀ x : A, (b, x)
    ∈ ars_reflexive_transitive_closure r → ∃ y : A, (x, y) ∈ r := by
  intro x hrtc
  rw [not_exists] at h
  specialize h x
  rw [ars_is_normalform_of, not_and_or] at h
  rcases h with h | h
  · contradiction
  · rw [ars_irreducible, Classical.not_not, ars_reducible] at h
    exact h

lemma aux_exists_infinity_chain_of_not_normalizing
  (r : Set (A × A)) :
  ¬ ars_normalizing r → ∃ f : ℕ → A, ∀ n : ℕ, (f n, f (n + 1)) ∈ r := by
  intro not_nor
  rw [ars_normalizing, not_forall] at not_nor
  obtain ⟨ b, hb ⟩ := not_nor

  -- subtypes are a bit spooky
  let Reachable := {x : A // (b, x) ∈ ars_reflexive_transitive_closure r }

  have reachable_next
    (x : Reachable) :
    ∃ y : Reachable, (x.val, y.val) ∈ r := by
    have xp := x.property
    have hnext := aux_exists_next_of_not_normalizing r b hb x xp
    obtain ⟨ y', h ⟩ := hnext
    have prop :  (b, y') ∈ ars_reflexive_transitive_closure r := by
      rw [ars_reflexive_transitive_closure]
      unfold ars_reflexive_transitive_closure at xp
      -- these two lines are tricky
      rcases Set.mem_iUnion.mp xp with ⟨ n, hxN ⟩
      refine Set.mem_iUnion.mpr ?_
      use n + 1
      rw [ars_power, comp]
      simp
      use x
    use ⟨ y', prop ⟩

  let f : ℕ → Reachable := Nat.rec
    ⟨ b, (by
      rw [ars_reflexive_transitive_closure]
      simp
      use 0
      rw [ars_power]
      simp
    )⟩
    (fun _ x => Classical.choose (reachable_next x))

  let f_loose : ℕ → A := fun n => (f n).val
  use f_loose
  intro n

  -- crazy, that this works in such a compact form
  exact Classical.choose_spec (reachable_next (f n))

lemma ars_terminating_normalizing (r: Set (A × A)) :
  ars_terminating r → ars_normalizing r := by
  intro ht
  by_contra not_nor
  have chain := aux_exists_infinity_chain_of_not_normalizing r not_nor
  contradiction

end ARS
