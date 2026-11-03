import FactoryRealization
import FactoryBatchPreparation
import FactoryCodingBounds
import FactoryFormationBudgets
import FactoryCodingSuccess
import FactoryDefectLedger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.CacheFactoryExact
open History FactoryRegisters FactoryPhysicalHamiltonian

def spectralSize {d : ℕ} (β : ℝ) (q : Density (Fin d)) : ℝ :=
  ∑ i,|(FactoryGibbs.tangent β q).hermitian.eigenvalues i|

theorem realizes {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef) (C : SmallResidueCoding τ) (n : ℕ)
    (hR : Real.log (C.residue n : ℝ) ≤ (n+1 : ℝ)) (η f : ℝ) (hη : 0 < η) (hf : 0 < f) :
    let A := FactoryCodingBounds.constant β d (spectralSize β q)
    ∃ (F : Formation β τ q (n+1)) (b : Budget),
      F.debit=FactoryFamilyRates.debit β τ q C (n+1) ∧
      traceDistance F.output (tensorPower τ.matrix (n+1)) ≤ FactoryFamilyRates.error C (n+1) ∧
      Driven.Meets F.hardware b ∧ b.productError ≤ η ∧ b.controllerEnergy ≤ η ∧
      b.controllerEntropy ≤ η ∧ b.batteryEntropy ≤ η ∧ b.failureProbability ≤ f ∧
      b.absoluteTail ≤ (n+1 : ℝ)*A*f ∧
      (∀ z (t : Tester F.schedule z), |Driven.defect F.hardware t| ≤
        (n+1 : ℝ)*A*(FactoryFamilyRates.error C (n+1)+f)) ∧ Driven.CapitalCharged F.hardware ∧
      F.hardware.w=16 ∧ F.hardware.HC.matrix=0 ∧
      (∀ z (t : Tester F.schedule z),
        ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin z)),
          FactoryControllerReturn.wholeState F.hardware t=F.hardware.controller.matrix ⊗ₖ σ.matrix) := by
  dsimp only
  let Λ := spectralSize β q
  let A := FactoryCodingBounds.constant β d Λ
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hG : 0 ≤ FactoryCodingBounds.gapConstant β d Λ :=
    FactoryCodingBounds.gapConstant_nonneg β hβ d hd Λ hΛ
  have hA : 0 ≤ A := by dsimp [A,FactoryCodingBounds.constant]; positivity
  have hGA : FactoryCodingBounds.gapConstant β d Λ ≤ A := by
    dsimp [A,FactoryCodingBounds.constant]; linarith
  have h4A : 4*Λ ≤ A := by dsimp [A,FactoryCodingBounds.constant]; linarith
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin (C.residue n)) := ⟨⟨0,C.residue_pos n⟩⟩
  let a := (Fin (n+1) → Fin d) × Fin (C.residue n)
  let D := Fintype.card a
  have hD : 0 < D := Fintype.card_pos
  let e : Fin D ≃ a := (Fintype.equivFin a).symm
  let batch := W2.tensorFamilyDensity (fun _ : Fin (n+1) => q)
  let Eg := FactoryBatchPreparation.eigenEnergy hd β q (n+1)
  let Ec := energy (tensorHamiltonian (tangentHamiltonian β q) (n+1)) (FactoryRate.decoded C n).matrix
  let x1 := -Eg-1
  let x2 := -Real.log ((D : ℝ)/C.rank n)/β
  let x3 := Eg-Ec
  let x4 := Real.log ((D : ℝ)/C.residue n)/β-1
  let P := FactoryBatchPreparation.projection hd β q (n+1)
  let V := (C.unitary n).submatrix e e
  have hV : IsUnitary V := unitary_submatrix e (C.unitary_isUnitary n)
  obtain ⟨δ,hδ,hreal⟩ := FactoryFormationBudgets.realizes hd (Nat.succ_pos n) hD (C.residue_pos n)
    β hβ τ q hq η f hη hf.le
  let ε := min (δ/8) (min (f/8) (min (1/2) (1/(n+2 : ℝ))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε ≤ δ/8 := min_le_left _ _
  have hεf : ε ≤ f/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hεhalf : ε ≤ 1/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεrate : ε ≤ 1/(n+2 : ℝ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 2*ε+ε+ε ≤ min δ f := le_min (by linarith) (by linarith)
  obtain ⟨C1,hcon1,hprep⟩ := FactoryBatchPreparation.prepare hd β hβ q hq (n+1) ε hε
  obtain ⟨hw1,hs1,he1⟩ := hprep batch
  let U1 := FactoryPreparationTransport.gate (FactoryBatchSpectrum.index d (n+1)) C1
  have hu1 : IsUnitary U1 := FactoryPreparationTransport.unitary _ C1
  obtain ⟨C2,hw2,hacc2⟩ := FactoryCodingSuccess.coding_output hd β hβ τ C n ε hε
  have hacc : traceDistance (partialRight ((evolve V (partialRight
      (FactoryFlatRun.state C2 (FactoryFormation.flat D hD)).matrix)).submatrix e.symm e.symm))
      (tensorPower τ.matrix (n+1)) ≤ C.error n+ε := by
    have hev := FactoryEnergyTransport.evolve_inverse e.symm (C.unitary n)
      (partialRight (FactoryFlatRun.state C2 (FactoryFormation.flat D hD)).matrix)
    simp only [Equiv.symm_symm] at hev
    calc
      _ = traceDistance (partialRight (evolve (C.unitary n)
          ((partialRight (FactoryFlatRun.state C2 (FactoryFormation.flat D hD)).matrix).submatrix
            e.symm e.symm))) (tensorPower τ.matrix (n+1)) :=
        congrArg (fun M : Mat a => traceDistance (partialRight M) (tensorPower τ.matrix (n+1))) hev
      _ ≤ C.error n+ε := hacc2
  obtain ⟨C4,F,b,hF,hdebit,haccF,hmeets,hproduct,hCE,hCS,hBE,hfail,htail,hcapital⟩ :=
    hreal C1.r C2.r C1.r_pos C2.r_pos C1.HR C2.HR x1 x2 x3 e P
      (FactoryBatchPreparation.projection_hermitian hd β q (n+1))
      (FactoryBatchPreparation.projection_idempotent hd β q (n+1))
      (FactoryBatchPreparation.projection_trace hd β q (n+1))
      U1 C2.U V hu1 C2.unitary hV ε ε ε hε.le hε (by linarith) hsmall (C.error n+ε)
      hs1 hw1 hw2 hacc
  have hnorm : ‖tensorHamiltonian (tangentHamiltonian β q) (n+1)‖ ≤ (n+1 : ℝ)*Λ := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      FactoryEnergy.tensor_norm_bound (FactoryGibbs.tangent β q) (n+1)
  have hEg : |Eg| ≤ (n+1 : ℝ)*Λ := by
    simpa only [Nat.cast_add,Nat.cast_one] using FactoryBatchPreparation.eigen_bound hd β q (n+1)
  have hEc : |Ec| ≤ (n+1 : ℝ)*Λ :=
    (density_energy_abs_le _ (FactoryRate.decoded C n)).trans hnorm
  have hgap := FactoryCodingBounds.gap_bound hd β hβ τ C n Λ Eg Ec hΛ hR hEg hEc
  have hdebit' : F.debit=FactoryFamilyRates.debit β τ q C (n+1) := by
    rw [hdebit]
    unfold FactoryFamilyRates.debit
    simp only [Nat.add_sub_cancel]
    have hDn : (D : ℝ)≠0 := by exact_mod_cast hD.ne'
    have hKn : (C.rank n : ℝ)≠0 := by exact_mod_cast (C.rank_pos n).ne'
    have hRn : (C.residue n : ℝ)≠0 := by exact_mod_cast (C.residue_pos n).ne'
    dsimp only [x1,x2,x3,Eg,Ec]
    rw [Real.log_div hDn hKn,Real.log_div hDn hRn]
    push_cast
    simp only [Nat.add_sub_cancel,Nat.succ_sub_one]
    ring
  have herr : FactoryFamilyRates.error C (n+1)=C.error n+1/(n+2 : ℝ) := by
    simp only [FactoryFamilyRates.error,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    congr 2
    ring
  have htail' : b.absoluteTail ≤ (n+1 : ℝ)*A*f := by
    calc _ ≤ (|x1|+|x2|+|x3|+|x4|)*f := htail
         _ ≤ ((n+1 : ℝ)*FactoryCodingBounds.gapConstant β d Λ)*f :=
           mul_le_mul_of_nonneg_right hgap hf.le
         _ ≤ (n+1 : ℝ)*A*f := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left hGA (by positivity)) hf.le
  have hdef : ∀ z (t : Tester F.schedule z), |Driven.defect F.hardware t| ≤
      (n+1 : ℝ)*A*(FactoryFamilyRates.error C (n+1)+f) := by
    subst F
    intro z t
    have hc2 := FactoryEnergyTransport.zero_conserves C2
    have hc4 := FactoryEnergyTransport.zero_conserves C4
    have hl := FactoryDefectLedger.exact_ledger hd (Nat.succ_pos n) hD C1.r_pos C2.r_pos C4.r_pos
      β hβ.ne' τ q hq C1.HR C2.HR C4.HR x1 x2 x4 Eg Ec e U1 C2.U V C4.U
      hu1 C2.unitary hV C4.unitary hcon1 hc2 hc4 z t
    have ha := FactoryPreparedEnergy.output_energy_error
      (tensorHamiltonian (tangentHamiltonian β q) (n+1)) _ (FactoryRate.decoded C n).matrix
      (tensorPower τ.matrix (n+1)) ((n+1 : ℝ)*Λ) (C.error n) ε
      (by positivity) hnorm (C.error_nonneg n) hε.le haccF (C.approximation n)
    have hb : |Eg-energy (tensorHamiltonian (tangentHamiltonian β q) (n+1))
        (partialRight (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C1.HR))))| ≤
        2*((n+1 : ℝ)*Λ)*ε := by
      simpa only [Nat.cast_add,Nat.cast_one] using he1
    rw [hl]
    calc _ ≤ (n+1 : ℝ)*(4*Λ)*(C.error n+1/(n+2 : ℝ)) :=
           FactoryUniformBounds.corrected_error (n+1 : ℝ) Λ (C.error n) ε (1/(n+2 : ℝ))
             (by positivity) hΛ (C.error_nonneg n) hε.le hεrate _ _ ha hb
         _ ≤ (n+1 : ℝ)*A*(C.error n+1/(n+2 : ℝ)) :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4A (by positivity))
             (add_nonneg (C.error_nonneg n) (by positivity))
         _ ≤ (n+1 : ℝ)*A*(FactoryFamilyRates.error C (n+1)+f) := by
           rw [herr]
           apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hwork : F.hardware.w=16 := by subst F; rfl
  have hzero : F.hardware.HC.matrix=0 := by subst F; rfl
  have hreturn : ∀ z (t : Tester F.schedule z),
      ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin z)),
        FactoryControllerReturn.wholeState F.hardware t=F.hardware.controller.matrix ⊗ₖ σ.matrix := by
    subst F
    exact FactoryPackedReturn.whole_product hd (Nat.succ_pos n) hD C1.r_pos C2.r_pos C4.r_pos
      β hβ.ne' τ q hq C1.HR C2.HR C4.HR x1 x2 x3 x4 e U1 C2.U V C4.U
      hu1 C2.unitary hV C4.unitary
  refine ⟨F,b,hdebit',?_,hmeets,?_,?_,?_,hBE,hfail,htail',hdef,hcapital,hwork,hzero,hreturn⟩
  · rw [herr]
    exact haccF.trans (by linarith)
  · rw [hproduct]; exact hη.le
  · rw [hCE]; exact hη.le
  · rw [hCS]; exact hη.le

theorem family {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef) (C : SmallResidueCoding τ) :
    ∃ (a err : ℕ → ℝ) (A : ℝ), 0≤A ∧
      Tendsto a atTop (𝓝 (faithfulRelativeEntropy τ.matrix q.matrix/β)) ∧
      Vanishes err ∧ (∀ m,0≤err m) ∧
      ∀ᶠ m : ℕ in atTop, ∀ η f : ℝ, 0<η → 0<f →
        ∃ (F : Formation β τ q m) (b : Budget), F.debit=a m ∧
          traceDistance F.output (tensorPower τ.matrix m)≤err m ∧ Driven.Meets F.hardware b ∧
          b.productError≤η ∧ b.controllerEnergy≤η ∧ b.controllerEntropy≤η ∧
          b.batteryEntropy≤η ∧ b.failureProbability≤f ∧ b.absoluteTail≤(m : ℝ)*A*f ∧
          (∀ z (t : Tester F.schedule z), |Driven.defect F.hardware t|≤(m : ℝ)*A*(err m+f)) ∧
          Driven.CapitalCharged F.hardware ∧ F.hardware.w=16 ∧ F.hardware.HC.matrix=0 ∧
          (∀ z (t : Tester F.schedule z),
            ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin z)),
              FactoryControllerReturn.wholeState F.hardware t=F.hardware.controller.matrix ⊗ₖ σ.matrix) := by
  let Λ := spectralSize β q
  let A := FactoryCodingBounds.constant β d Λ
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hG := FactoryCodingBounds.gapConstant_nonneg β hβ d hd Λ hΛ
  have hA : 0 ≤ A := by dsimp [A,FactoryCodingBounds.constant]; positivity
  refine ⟨FactoryFamilyRates.debit β τ q C,FactoryFamilyRates.error C,A,hA,
    FactoryFamilyRates.debit_limit β τ q C,FactoryFamilyRates.error_vanishes C,
    FactoryFamilyRates.error_nonneg C,?_⟩
  have hr := FactoryFamilyRates.predecessor_tendsto.eventually (FactoryUniformBounds.residue_eventually C)
  filter_upwards [hr,eventually_ge_atTop 1] with m hmR hm
  intro η f hη hf
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  have hR : Real.log (C.residue n : ℝ) ≤ (n+1 : ℝ) := by simpa using hmR
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ,A,Λ] using
    realizes hd β hβ τ q hq C n hR η f hη hf

end ScheduleLaw.Blueprint.CacheFactoryExact
