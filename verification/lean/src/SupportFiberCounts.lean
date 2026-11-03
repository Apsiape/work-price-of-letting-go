import SupportShells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open scoped BigOperators
namespace ScheduleLaw.Blueprint.SupportFiberCounts

/-- Cardinality of a literal bath fiber, retaining all degeneracy labels. -/
theorem bath_fiber_count {t : Type} [Fintype t] (g : t → ℕ) (p : t → Prop) :
    Fintype.card {b : SupportTiles.Bath g // p b.1} = ∑ j,if p j then g j else 0 := by
  classical
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p j <;> simp [hj]

/-- An injective tile label allows at most one occupied tile in each fiber. -/
theorem bath_fiber_upper {t c : Type} [Fintype t] (g : t → ℕ)
    (p : t → Prop) (label : t → c) (hl : Function.Injective label)
    (u : c) (B : ℝ) (hB : 0≤B)
    (hg : ∀ j,p j → label j=u → (g j : ℝ) ≤ B) :
    (Fintype.card {b : SupportTiles.Bath g // p b.1 ∧ label b.1=u} : ℝ) ≤ B := by
  classical
  have hc : Fintype.card {b : SupportTiles.Bath g // p b.1 ∧ label b.1=u} =
      ∑ j,if p j ∧ label j=u then g j else 0 := by
    convert bath_fiber_count g (fun j => p j ∧ label j=u) using 1 <;> congr!
  rw [hc]
  by_cases he : ∃ j,p j ∧ label j=u
  · obtain ⟨j,hj,hju⟩ := he
    have hs : (∑ k : t,if p k ∧ label k=u then g k else 0) = g j := by
      rw [Finset.sum_eq_single j]
      · simp [hj,hju]
      · intro k _ hkj
        have hku : label k ≠ u := by intro h; exact hkj (hl (h.trans hju.symm))
        simp [hku]
      · simp
    rw [hs]
    exact hg j hj hju
  · have hs : (∑ k : t,if p k ∧ label k=u then g k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk : ¬(p k ∧ label k=u) := fun h => he ⟨k,h⟩
      simp [hk]
    rw [hs,Nat.cast_zero]
    exact hB

/-- Each available tile contributes every one of its target columns. -/
theorem bath_fiber_lower {t : Type} [Fintype t] (g : t → ℕ) (p : t → Prop)
    (j : t) (hj : p j) :
    g j ≤ Fintype.card {b : SupportTiles.Bath g // p b.1} := by
  classical
  rw [bath_fiber_count]
  have hs := Finset.single_le_sum (f := fun k : t => if p k then g k else 0)
    (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa only [if_pos hj] using hs

/-- Cardinality separates system labels from each actual bath fiber. -/
theorem system_bath_fiber_count {a t : Type} [Fintype a] [Fintype t]
    (g : t → ℕ) (p : a → t → Prop) :
    Fintype.card {x : a × SupportTiles.Bath g // p x.1 x.2.1} =
      ∑ i,Fintype.card {b : SupportTiles.Bath g // p i b.1} := by
  classical
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]

end ScheduleLaw.Blueprint.SupportFiberCounts
