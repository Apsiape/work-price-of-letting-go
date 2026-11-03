import FactoryBattery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryProbability
open History

/-- An ordinary commuting flag union bound for any coherent battery state.
The conclusion uses the literal joint nominal label. -/
theorem failure_union {a k : Type} [Fintype a] [Fintype k] [DecidableEq a]
    (ρ : Density a) (nom : a) (F : k → a → Prop) [∀ i, DecidablePred (F i)]
    (hcover : ∀ j,j≠nom → ∃ i,¬F i j) :
    1-(ρ.matrix nom nom).re ≤
      ∑ i : k, ∑ j : a, if F i j then 0 else (ρ.matrix j j).re := by
  have hi (j : a) : (ρ.matrix j j).re-(if j=nom then (ρ.matrix j j).re else 0) ≤
      ∑ i : k, if F i j then 0 else (ρ.matrix j j).re := by
    by_cases hj : j=nom
    · simp only [hj,if_true,sub_self]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [FactoryBattery.diagonal_nonneg])
    · obtain ⟨i,hi⟩ := hcover j hj
      simp only [if_neg hj,sub_zero]
      calc
        _ = (if F i j then 0 else (ρ.matrix j j).re) := by rw [if_neg hi]
        _ ≤ ∑ i : k, if F i j then 0 else (ρ.matrix j j).re :=
          Finset.single_le_sum (f:=fun i => if F i j then 0 else (ρ.matrix j j).re)
            (fun i _ => by dsimp only; split_ifs <;> simp [FactoryBattery.diagonal_nonneg])
            (Finset.mem_univ i)
  calc
    _ = ∑ j : a,((ρ.matrix j j).re-(if j=nom then (ρ.matrix j j).re else 0)) := by
      rw [Finset.sum_sub_distrib,FactoryBattery.diagonal_sum]
      simp
    _ ≤ ∑ j : a, ∑ i : k, if F i j then 0 else (ρ.matrix j j).re :=
      Finset.sum_le_sum (fun j _ => hi j)
    _ = _ := Finset.sum_comm

/-- The source-preparation and extractor failure are counted separately.
No conditional independence of the coding residue is needed. -/
theorem four_stage_failure (ε₁ ε₂ ε₄ p₁ p₂ p₄ fail : ℝ)
    (hε₁ : 0≤ε₁) (hε₄ : 0≤ε₄)
    (h₁ : 1-ε₁≤p₁) (h₂ : 1-ε₂≤p₂) (h₄ : (1-ε₄)*(1-ε₁)≤p₄)
    (hu : fail≤(1-p₁)+(1-p₂)+(1-p₄)) :
    fail≤2*ε₁+ε₂+ε₄ := by
  nlinarith [mul_nonneg hε₁ hε₄]

end ScheduleLaw.Blueprint.FactoryProbability
