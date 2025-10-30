import ATPInLean.Sections.«02_AbstractReductionSystem»

-- ===================================================
-- More definitions, reusing from matlib if possible
-- ===================================================

namespace Orderings

variable {A : Type*}
open ARS

-- convert a ordering from the lecture to lean
def from_GT (R : Set (A × A)) :=
  fun a b => (b, a) ∈ R

def transgen_mem_iff_ars_transitive_closure
  (R: Set (A × A)) :
  (from_GT (ars_transitive_closure R)) = Relation.TransGen (from_GT R) := by
  funext a b; apply propext
  constructor
  · -- start with helper
    have aux : ∀ (n : ℕ ) (x y : A) , (y, x) ∈ ars_power (n + 1) R →
      Relation.TransGen (from_GT R) x y := by
      intro n
      induction n with
      | zero =>
          intro x y h
          simp [ars_power, comp] at h
          exact Relation.TransGen.single h
      | succ n ih =>
          intro x z ⟨ y, ⟨ l, r ⟩ ⟩
          specialize ih y z l
          exact Relation.TransGen.head r ih

    simp [from_GT]
    intro h
    rw [ars_transitive_closure, Set.mem_iUnion] at h
    obtain ⟨ n, hn ⟩ := h
    exact aux n a b hn

  · -- TransGen (from_GT R) a b ⇒ (b,a) ∈ TC(R)
    intro h
    simp [from_GT]
    exact @Relation.TransGen.trans_induction_on
      (motive := @fun a b _ => (b, a) ∈ ars_transitive_closure R)
      (r := (from_GT R))
      (α := A)
      (h := h)
      (a := a) (b := b)
      (single := @fun a b h => by
        simp [ars_transitive_closure]
        refine ⟨ 0, ?_ ⟩
        simp [ars_power, comp]
        exact h
      )
      (trans := @fun x y z h₁ h₂ m₁ m₂ => by
        simp at m₁ m₂ ⊢
        exact ars_transitive_closure_trans R z y x m₂ m₁
      )

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
  · -- use terminating to follow well founded ness
    have h: WellFounded (from_GT R) := by
      apply WellFounded.intro
      by_contra hn
      rw [not_forall] at hn
      obtain ⟨ x, hx ⟩ := hn

      let Inaccessible := {i // ¬ Acc (from_GT R) i}

      have has_step : ∀ p : Inaccessible,
        ∃ y, (from_GT R) y p.1 ∧ ¬ Acc (from_GT R) y := by
        intro p
        obtain ⟨ i, hi ⟩ := p
        by_contra n
        rw [not_exists] at n
        apply hi
        refine Acc.intro (x := i) ?_
        intro y hy
        specialize n y
        by_contra t
        apply n
        exact ⟨ hy, t ⟩

      let g : ℕ → Inaccessible :=
        Nat.rec
          ⟨ x, hx ⟩
          (fun _ p => by
            let pr := has_step p
            let y := Classical.choose pr
            let hy := Classical.choose_spec pr
            exact ⟨ y, hy.2 ⟩
          )
      let f : ℕ → A := fun n => (g n).1
      unfold ars_terminating at ht
      apply ht
      use f
      intro n
      specialize has_step (g n)
      -- I'm still a little bit confused how simp can look through recursive definitions
      exact (Classical.choose_spec has_step).left

    -- reusing mathlib here, otherwise this would be quite a pain
    have h' := WellFounded.transGen h

    rwa [transgen_mem_iff_ars_transitive_closure]

end Orderings
