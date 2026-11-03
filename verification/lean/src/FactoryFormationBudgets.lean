import FactoryCircuitFailure
import FactoryPackedBudgets
import FactoryWorkPacking

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFormationBudgets
open History FactoryRegisters FactoryPacking FactoryPackedFormation FactoryPackedStock

/-- A uniform finite-battery tolerance can be chosen before the converter
baths. The actual initialized circuit then meets all six original budgets,
with exact controller return, literal debit and charged startup capital. -/
theorem realizes {d m D R : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D) (hR : 0 < R)
    (β : ℝ) (hβ : 0 < β) (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (η f : ℝ) (hη : 0 < η) (hf : 0 ≤ f) :
    ∃ δ : ℝ,0 < δ ∧
      ∀ (r1 r2 : ℕ) (hr1 : 0 < r1) (hr2 : 0 < r2)
        (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (x1 x2 x3 : ℝ)
        (e : Fin D ≃ (Fin m → Fin d) × Fin R)
        (P : Mat (Fin m → Fin d)) (hP : P.IsHermitian) (hPi : P*P=P) (htr : P.trace=1)
        (U1 : Mat ((Fin m → Fin d) × (Fin 2 × Fin r1)))
        (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
        (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V)
        (ε1 ε2 ε4 : ℝ) (hε1 : 0 ≤ ε1) (hε4 : 0 < ε4) (hε41 : ε4 ≤ 1)
        (hsmall : 2*ε1+ε2+ε4 ≤ min δ f) (err : ℝ),
        let batch := W2.tensorFamilyDensity (fun _ : Fin m => q)
        let code := FactoryFormation.flat D hD
        let γ1 := gibbsDensity hr1 β H1
        let γ2 := gibbsDensity hr2 β H2
        (1-ε1 ≤ energy P (partialRight
          (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix))))) →
        (1-ε1 ≤ energy ((1 : Mat (Fin m → Fin d)) ⊗ₖ
          (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin r1))))
          (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix)))) →
        (1-ε2 ≤ energy ((1 : Mat (Fin D)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin r2))))
          (evolve U2 (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix)))) →
        (traceDistance (partialRight ((evolve V (partialRight
          (evolve U2 (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix))))).submatrix e.symm e.symm))
          (tensorPower τ.matrix m)≤err) →
        ∃ (C4 : SupportConverter β (FiniteFlat.zeroHamiltonian D) (Real.log ((D : ℝ)/R)/β-1))
          (F : Formation β τ q m) (b : Budget),
          F=formation hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq H1 H2 C4.HR
            x1 x2 x3 (Real.log ((D : ℝ)/R)/β-1) (circuit e U1 U2 V C4.U)
            (by convert circuit_unitary e U1 U2 V C4.U hu1 hu2 hv C4.unitary using 1) ∧
          F.debit=-(x1+x2+x3+(Real.log ((D : ℝ)/R)/β-1))/(m : ℝ) ∧
          traceDistance F.output (tensorPower τ.matrix m)≤err ∧
          Driven.Meets F.hardware b ∧ b.productError=0 ∧ b.controllerEnergy=0 ∧
          b.controllerEntropy=0 ∧ b.batteryEntropy≤η ∧ b.failureProbability≤f ∧
          b.absoluteTail≤(|x1|+|x2|+|x3|+|Real.log ((D : ℝ)/R)/β-1|)*f ∧
          Driven.CapitalCharged F.hardware := by
  obtain ⟨δ,hδ,htol⟩ := FactoryBattery.entropy_tolerance FactoryPacking.nominal η hη
  refine ⟨δ,hδ,?_⟩
  intro r1 r2 hr1 hr2 H1 H2 x1 x2 x3 e P hP hPi htr U1 U2 V hu1 hu2 hv ε1 ε2 ε4 hε1 hε4 hε41 hsmall err
  dsimp only
  intro hprep hw1 hw2 hacc
  let batch := W2.tensorFamilyDensity (fun _ : Fin m => q)
  let code := FactoryFormation.flat D hD
  let γ1 := gibbsDensity hr1 β H1
  let γ2 := gibbsDensity hr2 β H2
  obtain ⟨C4,hfail⟩ := FactoryCircuitFailure.failure hD hR β hβ e P hP hPi htr
    code batch γ1 γ2 code U1 U2 V hu1 hu2 hv ε1 ε2 ε4 hε1 hε4 hε41 hprep hw1 hw2
  let γ4 := gibbsDensity C4.r_pos β C4.HR
  let U := circuit e U1 U2 V C4.U
  have hU : IsUnitary U := by convert circuit_unitary e U1 U2 V C4.U hu1 hu2 hv C4.unitary using 1
  let ρ := FactoryCircuitFailure.state e code batch γ1 γ2 γ4 code U1 U2 V C4.U hu1 hu2 hv C4.unitary
  let x4 := Real.log ((D : ℝ)/R)/β-1
  let M := |x1|+|x2|+|x3|+|x4|
  have hM : 0 ≤ M := by positivity
  let F := formation hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq H1 H2 C4.HR
    x1 x2 x3 x4 U hU
  have hbat : ∀ z (t : Tester F.schedule z), Driven.batteryFinal F.hardware t=
      (FactoryWorkState.density ρ).matrix.submatrix workEquiv.symm workEquiv.symm := by
    intro z t
    exact FactoryWorkPacking.output hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq
      H1 H2 C4.HR x1 x2 x3 x4 U hU z t
  have hp : ∀ z (t : Tester F.schedule z),
      1-(Driven.batteryFinal F.hardware t F.hardware.nominalLevel F.hardware.nominalLevel).re ≤ min δ f := by
    intro z t
    change 1-(Driven.batteryFinal F.hardware t FactoryPacking.nominal FactoryPacking.nominal).re≤_
    rw [hbat z t]
    simpa only [Matrix.submatrix_apply,FactoryPacking.nominal,Equiv.symm_apply_apply] using hfail.trans hsmall
  have hreturn : ∀ z (t : Tester F.schedule z),
      ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin z)),
        FactoryControllerReturn.wholeState F.hardware t=F.hardware.controller.matrix ⊗ₖ σ.matrix := by
    exact FactoryPackedReturn.whole_product hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq
      H1 H2 C4.HR x1 x2 x3 x4 e U1 U2 V C4.U hu1 hu2 hv C4.unitary
  let b := FactoryDrivenBudgets.budget η f M
  have hmeets : Driven.Meets F.hardware b := by
    refine ⟨⟨le_rfl,le_rfl,le_rfl,hη.le,hf,mul_nonneg hM hf⟩,?_⟩
    intro z t
    obtain ⟨σ,hσ⟩ := hreturn z t
    obtain ⟨hc,he,hs⟩ := FactoryControllerReturn.exact_returns F.hardware t σ hσ
    have hpδ := (hp z t).trans (min_le_left _ _)
    have hpf := (hp z t).trans (min_le_right _ _)
    have hent : entropy (Driven.batteryFinal F.hardware t)≤η :=
      htol (FactoryDrivenBudgets.batteryDensity F.hardware t) hpδ
    have hgap (j : Fin F.hardware.w) :
        |F.hardware.batteryEnergy j-F.hardware.batteryEnergy F.hardware.nominalLevel|≤M :=
      FactoryPackedBudgets.four_bit_gap x1 x2 x3 x4 j
    have ht := (FactoryBattery.absolute_tail (FactoryDrivenBudgets.batteryDensity F.hardware t)
      F.hardware.batteryEnergy F.hardware.nominalLevel M hgap).trans
        (mul_le_mul_of_nonneg_left hpf hM)
    exact ⟨by simp [hc,b,FactoryDrivenBudgets.budget],by simp [he,b,FactoryDrivenBudgets.budget],
      by simp [hs,b,FactoryDrivenBudgets.budget],hent,hpf,ht⟩
  have hout : F.output=partialRight ((evolve V (partialRight
      (evolve U2 (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix))))).submatrix e.symm e.symm) := by
    rw [FactoryFormedOutput.output hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq
      H1 H2 C4.HR x1 x2 x3 x4 U hU]
    rw [FactoryInitializer.circuit_output e code batch γ1 γ2 γ4 code U1 U2 V C4.U hu1 C4.unitary]
  refine ⟨C4,F,b,rfl,?_,?_,hmeets,rfl,rfl,rfl,le_rfl,le_rfl,le_rfl,?_⟩
  · exact debit hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq H1 H2 C4.HR x1 x2 x3 x4 U hU
  · rw [hout]
    exact hacc
  · exact charged hd hm hD hr1 hr2 C4.r_pos β hβ.ne' τ q hq H1 H2 C4.HR x1 x2 x3 x4 U hU

end ScheduleLaw.Blueprint.FactoryFormationBudgets
