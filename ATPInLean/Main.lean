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


-- ===================================================
-- More definitions, reusing from matlib if possible
-- ===================================================
namespace Orderings
variable {A : Type*}
open ARS

-- convert a ordering from the lecture to lean
def from_GT (R : Set (A × A)) :=
  fun a b => (b, a) ∈ R

-- general question: should I use classes?

-- Well-Foundedness and Termination
-- Lemma 1.3.1
-- the proof does not need that R is a ordering
lemma wellfounded_order_subset_ars_terminating
  (R: Set (A × A)) (S: Set (A × A)) (hs: S ⊆ R) :
  -- Use the inverse relation for WellFounded to rule out forward-infinite chains
  -- we use the reversed notation, as we are interested in forward chains
  WellFounded (from_GT R) → ars_terminating S
  := by
  intro wf
  unfold ars_terminating
  intro h
  obtain ⟨ f, hf ⟩ := h
  have ⟨ a, ha, hmin ⟩  := wf.has_min (Set.range f) ⟨ f 0, by exact ⟨ 0, rfl ⟩ ⟩
  unfold from_GT at hmin
  have hn : ∃ n : ℕ, f n = a := by
    exact ha -- damn
  obtain ⟨ n, np ⟩ := hn
  specialize hf n
  rw [np] at hf
  rw [Set.range] at hmin
  simp at hmin
  specialize hmin (n + 1)
  apply hmin
  exact hs hf

lemma terminating_then_wellfounded_partial_ordering
  (R: Set (A × A)) :
  ars_terminating R →
    IsStrictOrder A (from_GT (ars_transitive_closure R)) ∧
    WellFounded (from_GT (ars_transitive_closure R))
   := by
  intro ht
  let rel := (from_GT (ars_transitive_closure R))
  have a : IsTrans A rel := by
    constructor
    intro a b c
    unfold rel from_GT
    exact fun a_1 a_2 ↦ ars_transitive_closure_trans R c b a a_2 a_1
  have b: IsIrrefl A rel := by
    constructor
    intro a
    intro ra
    unfold rel from_GT ars_transitive_closure at ra
    rcases Set.mem_iUnion.mp ra with ⟨ n, hn ⟩
    obtain ⟨ g, ⟨ g0, g1, g2 ⟩ ⟩ := ars_path_function_between_two_transitive_elements R (n + 1) a a hn

    -- idx always stays within [0, n + 1)
    let idx : ℕ → ℕ := Nat.rec 0 (fun _ i => if i = n then 0 else i + 1)
    have idx_lt : ∀ k, idx k < n + 1 := by
      intro k; induction k with
      | zero => simp [idx]
      | succ k ih =>
        cases lt_or_eq_of_le (Nat.lt_succ_iff.mp ih) with
        | inl hklt =>
          -- I really don't understand how this simp is arriving at the correct solution
          -- ???
          -- but it works kinda
          simp [idx, (ne_of_lt hklt)]
          exact hklt
        | inr hEq =>
          -- if idx k = n, then idx (k+1) = 0 < n+1
          simp [idx, hEq]

    let f : ℕ → A := fun k => g (idx k)

    unfold ars_terminating at ht
    apply ht
    use f
    -- again, this works, but I don't know how to manually prove this
    grind
  constructor
  · constructor
  ·

    -- AI generated part, review and rewrite for better understanding
    -- AT LEAST IT WORKS!!!!!!!!
    -- REALLY NICE!!!!
    have h: WellFounded (from_GT R) := by
      classical
      -- Prove by contradiction: if not well-founded, build an infinite forward chain in R
      by_contra hWF
      -- From ¬WellFounded r we get ∃ a, ¬Acc r a
      have not_all_acc : ¬ (∀ a, Acc (from_GT R) a) := by
        intro allAcc
        exact hWF ⟨allAcc⟩
      have ⟨a0, ha0⟩ : ∃ a, ¬ Acc (from_GT R) a := by
        exact not_forall.mp not_all_acc
      -- From a point not accessible, there is a predecessor which is also not accessible
      have exists_pred_not_acc : ∀ x, ¬ Acc (from_GT R) x →
          ∃ y, (from_GT R) y x ∧ ¬ Acc (from_GT R) y := by
        intro x hx
        classical
        by_contra hno
        -- hno : ¬ ∃ y, (from_GT R) y x ∧ ¬ Acc (from_GT R) y
        have hforall : ∀ y, ¬ ((from_GT R) y x ∧ ¬ Acc (from_GT R) y) := by
          simpa [not_exists] using hno
        have hxacc : Acc (from_GT R) x := by
          refine Acc.intro (x := x) ?pred
          intro y hy
          have : ¬ ¬ Acc (from_GT R) y := by
            have hny : ¬ ((from_GT R) y x ∧ ¬ Acc (from_GT R) y) := hforall y
            by_contra hnotacc
            exact hny ⟨hy, hnotacc⟩
          exact not_not.mp this
        exact hx hxacc
      -- Build a sequence of non-accessible elements following predecessors
      let g : ℕ → {x // ¬ Acc (from_GT R) x} :=
        Nat.rec ⟨a0, ha0⟩ (fun _ p =>
          let ex := exists_pred_not_acc p.1 p.2
          ⟨Classical.choose ex, (Classical.choose_spec ex).2⟩)
      let f : ℕ → A := fun n => (g n).1
      have step_fromGT : ∀ n, (from_GT R) (f (n+1)) (f n) := by
        intro n
        -- by construction of g, the (n+1)-th element is a predecessor of the n-th
        simpa [f, g] using
          (Classical.choose_spec (exists_pred_not_acc (g n).1 (g n).2)).1
      -- This yields a forward infinite chain in R, contradicting termination
      have step_R : ∀ n, (f n, f (n+1)) ∈ R := by
        intro n; simpa [from_GT] using step_fromGT n
      unfold ars_terminating at ht
      apply ht
      refine ⟨f, ?_⟩
      intro n; exact step_R n

    have h': WellFounded (Relation.TransGen (from_GT R)) := by
      exact WellFounded.transGen h

    have h'' : WellFounded (from_GT (ars_transitive_closure R)) := by
      constructor
      obtain ⟨ ml ⟩ := h'
      intro a
      specialize ml a
      unfold from_GT at ml ⊢

      -- ml : Acc (Relation.TransGen (fun a b ↦ (b, a) ∈ R)) a
      -- Goal: Acc (fun a b ↦ (b, a) ∈ ars_transitive_closure R) a
      -- Helper: transitive closure membership implies a TransGen step sequence
      have tc_to_transGen : ∀ {x y : A}, (x, y)
          ∈ ars_transitive_closure R →
          Relation.TransGen (fun a b ↦ (b, a) ∈ R) y x := by
        intro x y hxy
        rcases Set.mem_iUnion.mp hxy with ⟨n, hn⟩
        -- Prove the statement for a fixed length n+1 by induction on n
        have tc_power_to_transGen : ∀ {x y : A} {n : ℕ},
            (x, y) ∈ ars_power (n + 1) R →
            Relation.TransGen (fun a b ↦ (b, a) ∈ R) y x := by
          intro x y n hn'
          induction n generalizing y with
          | zero =>
              -- ars_power (0+1) R = comp (ars_power 0 R) R
              unfold ars_power at hn'
              unfold comp at hn'
              rcases hn' with ⟨m, hm0, hR⟩
              -- From hm0 : (x, m) ∈ ars_power 0 R, deduce x = m
              have hm0' : x = m := by
                simpa [ars_power] using hm0
              -- Thus the step (m, y) ∈ R is actually (x, y) ∈ R
              have hxy' : (x, y) ∈ R := by
                simpa [hm0'] using hR
              -- Single step in TransGen for base relation (reversed direction)
              exact Relation.TransGen.single hxy'
          | succ n ih =>
              -- ars_power (n+2) R = comp (ars_power (n+1) R) R
              unfold ars_power at hn'
              unfold comp at hn'
              rcases hn' with ⟨mid, hPow, hStep⟩
              -- IH: TransGen from mid to x for a shorter path
              have t_mid_x : Relation.TransGen (fun a b ↦ (b, a) ∈ R) mid x := ih hPow
              -- One step from y to mid using hStep
              have step_y_mid : (fun a b ↦ (b, a) ∈ R) y mid := by
                -- by definition, this is (mid, y) ∈ R
                exact hStep
              -- Prepend the step
              exact Relation.TransGen.head step_y_mid t_mid_x
        -- Apply the helper to our concrete `n`
        exact tc_power_to_transGen hn

    -- Build Acc for the closure using Acc on TransGen
      refine Acc.ndrecOn ml (fun x hx ih => by
        -- We must show Acc (closure) x, given IH for all predecessors along TransGen of R
        refine Acc.intro (x := x) ?_
        intro y hy
        -- hy: (y, x) ∈ ars_transitive_closure R (note the closure is on pairs (a,b) with (b,a) ∈ ...)
        have hyT : Relation.TransGen (fun a b ↦ (b, a) ∈ R) y x := tc_to_transGen hy
        -- Use the induction hypothesis along the TransGen edge
        exact ih y hyT)

        -- #check Acc.ndrecOn

        -- Acc.ndrecOn.{u1, u2} {α : Sort u2} {r : α → α → Prop} {C : α → Sort u1} {a : α} (n : Acc r a)
    -- (m : (x : α) → (∀ (y : α), r y x → Acc r y) → ((y : α) → r y x → C y) → C x) : C a
    exact h''

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

end ExerciseSheet1
