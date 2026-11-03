import TesterCone

/-! A strictly positive flat point of the full abstract causal-prefix set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem partialRight_one {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    partialRight (1 : Mat (a × b)) = (Fintype.card b : ℂ) • (1 : Mat a) := by
  rw [← one_kronecker_one,partialRight_kron,trace_one]

theorem partialLeft_one {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    partialLeft (1 : Mat (a × b)) = (Fintype.card a : ℂ) • (1 : Mat b) := by
  rw [← one_kronecker_one,partialLeft_kron,trace_one]

theorem tracePrefixInputs_one {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : tracePrefixInputs b hb 1 =
      (outputDimension S (arrived S (recordTime b) \
        arrived S (recordTime (previousInput b hb))) : ℂ) • 1 := by
  unfold tracePrefixInputs traceNewInputs withNewOutputsFirst
  rw [submatrix_one_equiv,partialRight_one,registers_card]
  ext i j
  change _ * (1 : Mat (Record S (arrived S (recordTime (previousInput b hb)))
      (released S (recordTime b)))) _ _ = _
  simp only [one_apply,smul_apply,smul_eq_mul]
  simp only [(outputRefinement S (arrived S (recordTime (previousInput b hb)))
    (released S (recordTime (previousInput b hb))) (released S (recordTime b))
    (previous_outputs_subset b hb)).symm.injective.eq_iff]

def flatPrefixFamily {I : Inventory} (S : Schedule I) : PrefixMatrices S := fun b =>
  (outputDimension S (arrived S (recordTime b)) : ℂ)⁻¹ • 1

theorem flat_prefix_posDef {I : Inventory} (S : Schedule I) (b : InputBurst S) :
    (flatPrefixFamily S b).PosDef := by
  apply Matrix.PosDef.smul Matrix.PosDef.one
  exact inv_pos.mpr (by exact_mod_cast outputDimension_pos S (arrived S (recordTime b)))

theorem flat_prefix_first {I : Inventory} (S : Schedule I) (b : InputBurst S) :
    partialLeft (flatPrefixFamily S b) = 1 := by
  rw [flatPrefixFamily,ClassicalFlag.partialLeft_weight,partialLeft_one,registers_card,
    smul_smul,inv_mul_cancel₀ (by exact_mod_cast ne_of_gt (outputDimension_pos S _)),one_smul]

theorem flat_prefix_higher {I : Inventory} (S : Schedule I) (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : tracePrefixInputs b hb (flatPrefixFamily S b) =
      (1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ flatPrefixFamily S (previousInput b hb) := by
  rw [flatPrefixFamily,tracePrefixInputs_weight,tracePrefixInputs_one]
  have hd := outputDimension_refinement S _ _ (previous_inputs_subset b hb)
  have ho : (outputDimension S (arrived S (recordTime (previousInput b hb))) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (outputDimension_pos S _)
  have hn : (outputDimension S (arrived S (recordTime b) \
      arrived S (recordTime (previousInput b hb))) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (outputDimension_pos S _)
  rw [smul_smul,hd,Nat.cast_mul,mul_inv,mul_assoc,inv_mul_cancel₀ hn,mul_one]
  rw [flatPrefixFamily]
  ext i j
  simp only [smul_apply,smul_eq_mul,kroneckerMap_apply,one_apply,Prod.ext_iff]
  split_ifs <;> simp_all

theorem flat_prefix_causal {I : Inventory} (S : Schedule I) :
    IsCausalPrefixFamily S (flatPrefixFamily S) :=
  ⟨fun b => (flat_prefix_posDef S b).posSemidef,
    fun b _ => flat_prefix_first S b,fun b hb => flat_prefix_higher S b hb⟩

theorem causal_prefix_set_nonempty {I : Inventory} (S : Schedule I) :
    {Z : PrefixMatrices S | IsCausalPrefixFamily S Z}.Nonempty :=
  ⟨flatPrefixFamily S,flat_prefix_causal S⟩

end History
end ScheduleLaw
