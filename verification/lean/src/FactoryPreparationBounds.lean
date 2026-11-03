import FactoryConverterSuccess

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPreparationBounds
open History

theorem system_work_le_system {b t : Type} [Fintype b] [Fintype t]
    [DecidableEq b] [DecidableEq t] (P : Mat b) (hP : P.PosSemidef)
    (ρ : Density (b × (Fin 2 × t))) :
    energy (P ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t))) ρ.matrix ≤
      energy P (partialRight ρ.matrix) := by
  let W : Mat (Fin 2 × t) := SupportRun.level 1 ⊗ₖ (1 : Mat t)
  have hW : W.IsHermitian :=
    ((pureMatrix_positive (fun w : Fin 2 => if w=1 then 1 else 0)).kronecker
      (Matrix.PosSemidef.one : (1 : Mat t).PosSemidef)).isHermitian
  have hWi : W*W=W := by
    simp only [W,← mul_kronecker_mul,SupportRun.level_idem,one_mul]
  rw [← energy_kron_one]
  apply SupportEffect.energy_mono _ _ _ _ ρ.positive
  convert hP.kronecker (FactoryCoding.complement_positive W hW hWi) using 1
  ext i j
  simp only [Matrix.sub_apply,kroneckerMap_apply,W]
  ring

theorem eigen_hermitian {d : ℕ} (U : Mat (Fin d)) (i : Fin d) :
    (FactorySupport.eigenProjection U i).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  rw [isHermitian_diagonal_iff]
  intro j
  split_ifs <;> simp

theorem eigen_idempotent {d : ℕ} (U : Mat (Fin d)) (hU : IsUnitary U) (i : Fin d) :
    FactorySupport.eigenProjection U i*FactorySupport.eigenProjection U i=
      FactorySupport.eigenProjection U i := by
  let D : Mat (Fin d) := diagonal (fun j => if j=i then 1 else 0)
  have hD : D*D=D := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    split_ifs <;> norm_num
  let φ := Unitary.conjStarAlgAut ℂ (Mat (Fin d)) (⟨U,hU⟩ : unitaryGroup (Fin d) ℂ)
  change φ D*φ D=φ D
  rw [← map_mul,hD]

theorem eigen_trace {d : ℕ} (U : Mat (Fin d)) (hU : IsUnitary U) (i : Fin d) :
    (FactorySupport.eigenProjection U i).trace=1 := by
  rw [FactorySupport.eigenProjection,evolve,trace_mul_cycle,hU.1,one_mul]
  simp

/-- One actual preparation supplies both the eventual work flag and the
actual eigenprojection weight transferred into the extractor support. -/
theorem prepare_complete {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (U : Mat (Fin d)) (hU : IsUnitary U) (E : Fin d → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun j => (E j : ℂ))))
    (i : Fin d) (f : ℝ) (hf : 0 < f) :
    ∃ C : SupportConverter β H (-E i-Real.log (partition β H)/β-1),
      ∀ ρ : Density (Fin d),
      1-f ≤ energy ((1 : Mat (Fin d)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
        (FactoryFlatRun.state C ρ).matrix ∧
      1-f ≤ energy (FactorySupport.eigenProjection U i)
        (partialRight (FactoryFlatRun.state C ρ).matrix) := by
  obtain ⟨C,hC⟩ := FactoryConverterSuccess.prepare_local hd β hβ H U hU E hH i f hf
  refine ⟨C,fun ρ => ?_⟩
  have hp := hC ρ
  have hP := eigen_hermitian U i
  have hPi := eigen_idempotent U hU i
  exact ⟨hp.trans (FactoryConverterSuccess.system_work_le_work _ hP hPi _),
    hp.trans (system_work_le_system _ (FactoryCoding.projection_positive _ hP hPi) _)⟩

end ScheduleLaw.Blueprint.FactoryPreparationBounds
