/-
The paddedBurstAmplitude and exists_padded_burst_isometry declarations adapt
QIT/HigherOrder/Comb/Realization.lean from the read-only companion Lean-QIT
snapshot. Copyright (c) 2026 QuAIR. Authors: QuAIR Team. Apache 2.0; see
LICENSE-APACHE-2.0.txt. Imports, names, matrix bundle and positive-output
interface adapted for Lean 4.30. Other declarations are new for this relay.
Source SHA-256 is recorded in logs/round6/purification-port-provenance.json.
-/
import CombRealization
import PureFactor
import PurificationMatrix

/-! Canonical purifications of the actual causal-prefix matrices, and the
inverse-free, waste-retaining single-burst isometry step. These are proved
without CombRealization. The schedule-wide Tester assembly remains separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Braket
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

theorem density_purification_matrix {a : Type} [Fintype a] [DecidableEq a] (ρ : MState a) :
    partialRight (pureMatrix ρ.purify.vec) = ρ.m := by
  have h := congrArg MState.m ρ.purify_spec
  change partialRight (MState.pure ρ.purify).m = ρ.m at h
  rw [library_pure_matrix] at h
  exact h

def prefixPurification {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) :
    (Record S (arrived S (recordTime b)) (released S (recordTime b))) ×
      (Record S (arrived S (recordTime b)) (released S (recordTime b))) → ℂ :=
  (Real.sqrt (prefixDimension b : ℝ) : ℂ) • (statesOfCausalFamily S Z hZ b).purify.vec

theorem prefixPurification_gram {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) :
    partialRight (pureMatrix (prefixPurification S Z hZ b)) = Z b := by
  have hn : Complex.normSq (Real.sqrt (prefixDimension b : ℝ) : ℂ) = (prefixDimension b : ℝ) := by
    rw [Complex.normSq_ofReal,Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [prefixPurification,pureMatrix_scale,ClassicalFlag.partialRight_weight,
    density_purification_matrix,hn]
  change (prefixDimension b : ℂ) • ((prefixDimension b : ℂ)⁻¹ • Z b) = Z b
  rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (outputDimension_pos S _)),one_smul]

theorem prefixPurification_norm {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) :
    ∑ x, Complex.normSq (prefixPurification S Z hZ b x) = (prefixDimension b : ℝ) := by
  have ht := congrArg Matrix.trace (prefixPurification_gram S Z hZ b)
  rw [partialRight_trace,pureMatrix_trace,causal_prefix_trace S Z hZ b] at ht
  exact congrArg Complex.re ht

theorem first_prefix_purification_normalized {I : Inventory} (S : Schedule I)
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0 < S.visits) :
    ∑ x, Complex.normSq (prefixPurification S Z hZ (firstInputBurst S h) x) = 1 := by
  rw [prefixPurification_norm,first_dimension_one,Nat.cast_one]

def paddedBurstAmplitude {a m c d κ : Type} (B : Matrix (a × c) (d × κ) ℂ) :
    Matrix (a × c) (d × (κ ⊕ (m × c))) ℂ :=
  fun x y => Sum.elim (fun k => B x (y.1,k)) (fun _ => 0) y.2

/-- Equality of the required prefix purifications supplies an isometry on
the whole incoming memory/port. Padding keeps all original waste and adds
room to extend its action off the support. No inverse is taken. -/
theorem exists_padded_burst_isometry {a m c d κ : Type}
    [Fintype a] [DecidableEq a] [Fintype m] [DecidableEq m]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype κ] [DecidableEq κ] (A : Matrix a m ℂ) (B : Matrix (a × c) (d × κ) ℂ)
    (hGram : ∀ x y z z', (∑ v,∑ k, B (x,z) (v,k) * star (B (y,z') (v,k))) =
      if z = z' then ∑ v, A x v * star (A y v) else 0) :
    ∃ V : Matrix (d × (κ ⊕ (m × c))) (m × c) ℂ, Vᴴ * V = 1 ∧
      ∀ x z v k, paddedBurstAmplitude (m := m) B (x,z) (v,k) =
        ∑ w, A x w * V (v,k) (w,z) := by
  let A' : Matrix (a × c) (m × c) ℂ := fun x y => if x.2 = y.2 then A x.1 y.1 else 0
  have hcard : Fintype.card (m × c) ≤ Fintype.card (d × (κ ⊕ (m × c))) :=
    Fintype.card_le_of_injective (fun x : m × c => (Classical.choice inferInstance,Sum.inr x))
      (fun _ _ h => Sum.inr_injective (congrArg Prod.snd h))
  have hAA (x y : a × c) : (A' * A'ᴴ) x y =
      if x.2 = y.2 then ∑ v, A x.1 v * star (A y.1 v) else 0 := by
    change (∑ p : m × c, A' x p * star (A' y p)) = _
    simp only [A',Fintype.sum_prod_type]
    by_cases h : x.2 = y.2
    · simp [← h]
    · simp [h,ite_mul,apply_ite,eq_comm]
  have hBB (x y : a × c) :
      (paddedBurstAmplitude (m := m) B * (paddedBurstAmplitude (m := m) B)ᴴ) x y =
      ∑ v,∑ k, B x (v,k) * star (B y (v,k)) := by
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,paddedBurstAmplitude,
      Fintype.sum_prod_type,Fintype.sum_sum_type]
  have he : A' * A'ᴴ = paddedBurstAmplitude (m := m) B * (paddedBurstAmplitude (m := m) B)ᴴ := by
    ext x y
    rw [hAA,hBB]
    exact (hGram x.1 y.1 x.2 y.2).symm
  obtain ⟨V,hV,hF⟩ := gram_factor_isometry A' (paddedBurstAmplitude (m := m) B) he hcard
  refine ⟨V,hV,?_⟩
  intro x z v k
  have ht := congrFun₂ hF (x,z) (v,k)
  change paddedBurstAmplitude B (x,z) (v,k) = ∑ p : m × c, A' (x,z) p * V (v,k) p at ht
  simpa [A',Fintype.sum_prod_type,ite_mul] using ht

end ScheduleLaw.History
