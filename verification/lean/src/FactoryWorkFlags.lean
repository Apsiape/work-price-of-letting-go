import FactoryProbability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryWorkFlags
open History

abbrev Work := Fin 2 × Fin 2 × Fin 2 × Fin 2

def nominal : Work := (1,1,1,1)

def flag (i : Fin 4) (w : Work) : Fin 2 := ![w.1,w.2.1,w.2.2.1,w.2.2.2] i

def success (ρ : Density Work) (i : Fin 4) : ℝ :=
  ∑ w : Work, if flag i w=1 then (ρ.matrix w w).re else 0

theorem flag_failure (ρ : Density Work) (i : Fin 4) :
    (∑ w : Work,if flag i w=1 then 0 else (ρ.matrix w w).re)=1-success ρ i := by
  have hi (w : Work) : (if flag i w=1 then 0 else (ρ.matrix w w).re) =
      (ρ.matrix w w).re-(if flag i w=1 then (ρ.matrix w w).re else 0) := by
    split_ifs <;> ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib,FactoryBattery.diagonal_sum]
  rfl

theorem joint_failure (ρ : Density Work) :
    1-(ρ.matrix nominal nominal).re≤∑ i : Fin 4,(1-success ρ i) := by
  have hcover (w : Work) (hw : w≠nominal) : ∃ i : Fin 4,¬flag i w=1 := by
    by_contra h
    push Not at h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp only [flag,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.isValue] at h0 h1 h2 h3
    apply hw
    rcases w with ⟨w1,w2,w3,w4⟩
    simp_all [nominal]
  have hu := FactoryProbability.failure_union ρ nominal (fun i w => flag i w=1) hcover
  simpa only [flag_failure] using hu

/-- Actual sixteen-level battery state: the third register flips exactly,
and the three converter success bounds imply the literal joint-label bound. -/
theorem four_register_bound (ρ : Density Work) (ε₁ ε₂ ε₄ : ℝ)
    (hε₁ : 0≤ε₁) (hε₄ : 0≤ε₄)
    (h₁ : 1-ε₁ ≤ success ρ 0) (h₂ : 1-ε₂ ≤ success ρ 1)
    (h₃ : success ρ 2=1) (h₄ : (1-ε₄)*(1-ε₁) ≤ success ρ 3) :
    1-(ρ.matrix nominal nominal).re≤2*ε₁+ε₂+ε₄ := by
  apply FactoryProbability.four_stage_failure ε₁ ε₂ ε₄
    (success ρ 0) (success ρ 1) (success ρ 3) _ hε₁ hε₄ h₁ h₂ h₄
  have hu := joint_failure ρ
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hu
  change 1-(ρ.matrix nominal nominal).re ≤
    (1-success ρ 0)+((1-success ρ 1)+((1-success ρ 2)+(1-success ρ 3))) at hu
  rw [h₃] at hu
  linarith

end ScheduleLaw.Blueprint.FactoryWorkFlags
