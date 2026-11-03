import FactoryFlatRun
import FactorySupport
import FactoryCoding
import FactoryExtractGeneral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryConverterSuccess
open History

/-- Evaluate a reference-uniform converter certificate on its actual local
initialized run. Every failed column is retained. -/
theorem local_bound {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (P : Mat (Fin d)) (ρ : Density (Fin d)) (a : ℝ)
    (h : ∀ z (τ : Density (Fin d × Fin z)),
      a ≤ energy ((P ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z τ.matrix)) :
    a ≤ energy (P ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
      (FactoryFlatRun.state C ρ).matrix := by
  let σ := FactoryFormation.flat 1 (by decide)
  let τ : Density (Fin d × Fin 1) := ⟨ρ.matrix ⊗ₖ σ.matrix,
    ρ.positive.kronecker σ.positive,by rw [trace_kronecker,ρ.normalized,σ.normalized,one_mul]⟩
  have hh := h 1 τ
  change a ≤ energy _ (C.run 1 (ρ.matrix ⊗ₖ σ.matrix)) at hh
  rw [FactoryFlatRun.run_product,energy_kron_one,partialRight_kron,σ.normalized,one_smul] at hh
  exact hh

/-- Dropping only the system projection increases the actual successful work
probability. This is an operator comparison, not postselection. -/
theorem system_work_le_work {b t : Type} [Fintype b] [Fintype t]
    [DecidableEq b] [DecidableEq t] (P : Mat b) (hP : P.IsHermitian) (hPi : P*P=P)
    (ρ : Density (b × (Fin 2 × t))) :
    energy (P ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t))) ρ.matrix ≤
      energy ((1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t))) ρ.matrix := by
  apply SupportEffect.energy_mono _ _ _ _ ρ.positive
  convert (FactoryCoding.complement_positive P hP hPi).kronecker
    ((pureMatrix_positive (fun w : Fin 2 => if w=1 then 1 else 0)).kronecker
      (Matrix.PosSemidef.one : (1 : Mat t).PosSemidef)) using 1
  ext i j
  simp only [sub_apply,kroneckerMap_apply,SupportRun.level]
  ring

/-- The constructed preparation converter has its claimed actual local joint
success probability for every input density. -/
theorem prepare_local {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (U : Mat (Fin d)) (hU : IsUnitary U) (E : Fin d → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun j => (E j : ℂ))))
    (i : Fin d) (f : ℝ) (hf : 0 < f) :
    ∃ C : SupportConverter β H (-E i-Real.log (partition β H)/β-1),
      ∀ ρ : Density (Fin d),
      1-f ≤ energy (FactorySupport.eigenProjection U i ⊗ₖ
        (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) (FactoryFlatRun.state C ρ).matrix := by
  obtain ⟨C,hC⟩ := FactorySupport.prepare_eigenvector hd β hβ H U hU E hH i f hf
  exact ⟨C,fun ρ => local_bound C (FactorySupport.eigenProjection U i) ρ (1-f) hC⟩

/-- The general support extractor, evaluated on its actual local initialized
run for an arbitrary mixed code state. -/
theorem extract_local {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (P : Mat (Fin d)) (hP : P.IsHermitian) (hPi : P*P=P)
    (k : ℕ) (hk : 0 < k) (htr : P.trace=(k : ℂ)) (f : ℝ) (hf : 0 < f) :
    ∃ C : SupportConverter β (FiniteFlat.zeroHamiltonian d) (Real.log ((d : ℝ)/k)/β-1),
      ∀ ρ : Density (Fin d),
        (1-f)*energy P ρ.matrix ≤
          energy ((1 : Mat (Fin d)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
            (FactoryFlatRun.state C ρ).matrix := by
  obtain ⟨C,hC⟩ := FactorySupport.extract_support_general hd β hβ P hP hPi k hk htr f hf
  refine ⟨C,fun ρ => ?_⟩
  let σ := FactoryFormation.flat 1 (by decide)
  let τ : Density (Fin d × Fin 1) := ⟨ρ.matrix ⊗ₖ σ.matrix,
    ρ.positive.kronecker σ.positive,by rw [trace_kronecker,ρ.normalized,σ.normalized,one_mul]⟩
  have hh := hC 1 τ
  change (1-f)*energy (P ⊗ₖ (1 : Mat (Fin 1))) (ρ.matrix ⊗ₖ σ.matrix) ≤
    energy _ (C.run 1 (ρ.matrix ⊗ₖ σ.matrix)) at hh
  rw [FactoryFlatRun.run_product,energy_kron_one,energy_kron_one,partialRight_kron,
    partialRight_kron,σ.normalized,one_smul] at hh
  simpa only [one_smul] using hh

end ScheduleLaw.Blueprint.FactoryConverterSuccess
