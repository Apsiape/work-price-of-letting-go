import FactoryPreparedSupport
import FactoryPackedStock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryExtractorBound
open History FactoryRegisters FactoryFlagEffects

/-- Choose the actual general-input extractor and prove its success in the
complete circuit. Its support retains the entire physical coding residue. -/
theorem extract {b : Type} [Fintype b] [DecidableEq b] {D R r1 r2 : ℕ}
    (hD : 0 < D) (hR : 0 < R) (β : ℝ) (hβ : 0 < β)
    (e : Fin D ≃ b × Fin R) (P : Mat b) (hP : P.IsHermitian) (hPi : P*P=P) (htr : P.trace=1)
    (code : Density (Fin D)) (batch : Density b) (γ1 : Density (Fin r1))
    (γ2 : Density (Fin r2)) (fresh : Density (Fin D))
    (U1 : Mat (b × (Fin 2 × Fin r1))) (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V)
    (ε1 ε4 : ℝ) (hε4 : 0 < ε4) (hε41 : ε4 ≤ 1)
    (hprep : 1-ε1 ≤ energy P (partialRight
      (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix))))) :
    ∃ C4 : SupportConverter β (FiniteFlat.zeroHamiltonian D) (Real.log ((D : ℝ)/R)/β-1),
      (1-ε4)*(1-ε1) ≤
        success (FactoryRegisterFlags.flag 3) (evolve (circuit e U1 U2 V C4.U)
          (FactoryInitializer.matrix code batch γ1 γ2
            (FactoryPackedStock.gibbsDensity C4.r_pos β C4.HR) fresh)) := by
  let Q : Mat (Fin D) := (P ⊗ₖ (1 : Mat (Fin R))).submatrix e e
  have hQ : Q.IsHermitian := ((FactoryCoding.projection_positive P hP hPi).kronecker
    (Matrix.PosSemidef.one : (1 : Mat (Fin R)).PosSemidef)).isHermitian.submatrix e
  have hQi : Q*Q=Q := by
    simp only [Q,submatrix_mul_equiv,← mul_kronecker_mul,hPi,one_mul]
  have hQt : Q.trace=(R : ℂ) := by
    change ((P ⊗ₖ (1 : Mat (Fin R))).submatrix e e).trace=(R : ℂ)
    rw [submatrix_trace_equiv,trace_kronecker,htr,one_mul]
    simp
  obtain ⟨C4,hC4⟩ := FactoryConverterSuccess.extract_local hD β hβ Q hQ hQi R hR hQt ε4 hε4
  let γ4 := FactoryPackedStock.gibbsDensity C4.r_pos β C4.HR
  let ρ := FactoryFourthSuccess.codeState e code batch γ1 γ2 fresh U1 U2 V h1 h2 hV
  have hw : 1-ε1 ≤ energy Q ρ.matrix := by
    rw [FactoryPreparedSupport.support_weight e code batch γ1 γ2 γ4 fresh U1 U2 V h1 h2 hV P]
    exact hprep
  refine ⟨C4,?_⟩
  have hp : success (FactoryRegisterFlags.flag 3) (evolve (circuit e U1 U2 V C4.U)
      (FactoryInitializer.matrix code batch γ1 γ2 (FactoryPackedStock.gibbsDensity C4.r_pos β C4.HR) fresh))=
      energy ((1 : Mat (Fin D)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C4.r))))
        (FactoryFlatRun.state C4 ρ).matrix := by
    convert FactoryFourthSuccess.probability e code batch γ1 γ2 γ4 fresh U1 U2 V C4.U h1 h2 hV using 1
    unfold success effect
    congr 1
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
  rw [hp]
  exact (mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ 1-ε4)).trans (hC4 ρ)

end ScheduleLaw.Blueprint.FactoryExtractorBound
