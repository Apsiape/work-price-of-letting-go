import ClassicalFlag

/-! Exact entropy and handoff accounting for a retained classical source flag. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace ClassicalFlag

def carrierOnPayload (I : Inventory) (c : Fin I.count) : Mat (Payload I) :=
  fun p q => (if ∀ d, d ≠ c → p d = q d then 1 else 0) * (I.H c).matrix (p c) (q c)

theorem carrierEnergy_reduced {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (ρ : Mat (Global e r)) (c : Fin I.count) :
    carrierEnergy e ρ c = energy (carrierOnPayload I c) (partialRight (partialLeft ρ)) := by
  rw [carrierEnergy_as_observable,lifted_carrier_agrees]
  have he : liftTesterObservable e r (carrierObservable I r c) =
      (1 : Mat (Fin e.b)) ⊗ₖ (carrierOnPayload I c ⊗ₖ (1 : Mat (Fin r))) := by
    ext i j
    simp only [liftTesterObservable,carrierObservable,carrierOnPayload,submatrix_apply,
      kroneckerMap_apply,one_apply,Equiv.prodComm_apply]
    split_ifs <;> simp_all
  rw [he,energy_one_kron,energy_kron_one]

theorem energy_weight {a : Type} [Fintype a] (H ρ : Mat a) (p : ℝ) :
    energy H ((p : ℂ) • ρ) = p * energy H ρ := by
  simp [energy,Matrix.mul_smul,trace_smul]

theorem energy_state_add {a : Type} [Fintype a] (H ρ σ : Mat a) :
    energy H (ρ+σ) = energy H ρ + energy H σ := by
  simp [energy,mul_add,trace_add]

theorem partialRight_add {a p : Type} [Fintype p] (A B : Mat (a × p)) :
    partialRight (A+B) = partialRight A + partialRight B := by
  ext i j
  simp [partialRight,Finset.sum_add_distrib]

theorem carrierEnergy_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r)
    (n : ℕ) (c : Fin I.count) :
    carrierEnergy (extension e f δ hδ hδ1) (run (extension e f δ hδ hδ1) t n) c =
      (1-δ) * carrierEnergy e (run e t n) c + δ * carrierEnergy f (run f t n) c := by
  rw [carrierEnergy_reduced,run_branches,partialLeft_branches,partialRight_add,
    partialLeft_weight,partialLeft_weight,partialRight_weight,partialRight_weight,
    energy_state_add,energy_weight,energy_weight,carrierEnergy_reduced,carrierEnergy_reduced]

theorem handoff_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) :
    handoff (extension e f δ hδ hδ1) t = (1-δ) * handoff e t + δ * handoff f t := by
  unfold handoff
  simp_rw [carrierEnergy_branches]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

def binaryEntropy (δ : ℝ) : ℝ := Real.negMulLog (1-δ) + Real.negMulLog δ

theorem source_entropy {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    entropy (extension e f δ hδ hδ1).source.matrix =
      binaryEntropy δ + (1-δ) * entropy e.source.matrix + δ * entropy f.source.matrix := by
  change entropy ((block (((1-δ : ℝ) : ℂ) • e.source.matrix)
    ((δ : ℂ) • f.source.matrix)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  have he := (e.source.positive.smul
    (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hδ1,rfl⟩ : (0 : ℂ) ≤ ((1-δ : ℝ) : ℂ))).isHermitian
  have hf := (f.source.positive.smul
    (Complex.nonneg_iff.mpr ⟨hδ,rfl⟩ : (0 : ℂ) ≤ (δ : ℂ))).isHermitian
  rw [entropy_submatrix_equiv _ _ (block_hermitian _ _ he hf),
    block_entropy _ _ he hf,entropy_weight e.source (1-δ) (sub_nonneg.mpr hδ1),
    entropy_weight f.source δ hδ]
  unfold binaryEntropy
  ring

theorem output_entropy {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) :
    entropy (bodyOutput (extension e f δ hδ hδ1) t) =
      binaryEntropy δ + (1-δ) * entropy (bodyOutput e t) + δ * entropy (bodyOutput f t) := by
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  let σ : Density (Fin f.b) := ⟨bodyOutput f t,(bodyOutput_density f t).1,(bodyOutput_density f t).2⟩
  have he := (ρ.positive.smul
    (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hδ1,rfl⟩ : (0 : ℂ) ≤ ((1-δ : ℝ) : ℂ))).isHermitian
  have hf := (σ.positive.smul
    (Complex.nonneg_iff.mpr ⟨hδ,rfl⟩ : (0 : ℂ) ≤ (δ : ℂ))).isHermitian
  rw [bodyOutput_branches]
  change entropy ((block (((1-δ : ℝ) : ℂ) • ρ.matrix) ((δ : ℂ) • σ.matrix)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [entropy_submatrix_equiv _ _ (block_hermitian _ _ he hf),
    block_entropy _ _ he hf,entropy_weight ρ (1-δ) (sub_nonneg.mpr hδ1),entropy_weight σ δ hδ]
  unfold binaryEntropy
  ring

/-- Exact cancellation of flag entropy in the operational score. -/
theorem score_branches {I : Inventory} {S : Schedule I} (β : ℝ) (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) :
    score β (extension e f δ hδ hδ1) t = (1-δ) * score β e t + δ * score β f t := by
  unfold score
  rw [source_entropy,output_entropy,handoff_branches]
  ring

theorem score_bound {I : Inventory} {S : Schedule I} (β : ℝ) (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (g k : ℝ)
    (he : ∀ r (t : Tester S r), score β e t ≤ g)
    (hf : ∀ r (t : Tester S r), score β f t ≤ k) :
    ∀ r (t : Tester S r), score β (extension e f δ hδ hδ1) t ≤ g + δ * (k-g) := by
  intro r t
  rw [score_branches]
  calc (1-δ) * score β e t + δ * score β f t
      ≤ (1-δ) * g + δ * k := add_le_add
        (mul_le_mul_of_nonneg_left (he r t) (sub_nonneg.mpr hδ1))
        (mul_le_mul_of_nonneg_left (hf r t) hδ)
    _ = g + δ * (k-g) := by ring

end ClassicalFlag
end ScheduleLaw
