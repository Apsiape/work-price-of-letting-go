import PartnerMarginal
import ConsecutiveBursts

/-! Every higher causal prefix equation for the independently wired Gram
of an actual tester. The partial trace and both tensor factors are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def tracePrefixInputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val)
    (Z : Mat (Record S (arrived S (recordTime b)) (released S (recordTime b)))) :
    Mat (Registers S (newOutputs b hb) ×
      Record S (arrived S (recordTime (previousInput b hb)))
        (released S (recordTime (previousInput b hb)))) :=
  withNewOutputsFirst S (arrived S (recordTime (previousInput b hb)))
    (released S (recordTime (previousInput b hb))) (released S (recordTime b))
    (previous_outputs_subset b hb)
    (traceNewInputs S (arrived S (recordTime (previousInput b hb)))
      (arrived S (recordTime b)) (released S (recordTime b))
      (previous_inputs_subset b hb) Z)

theorem tracePrefixInputs_weight {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (Z : Mat (Record S (arrived S (recordTime b))
      (released S (recordTime b)))) (c : ℂ) :
    tracePrefixInputs b hb (c • Z) = c • tracePrefixInputs b hb Z := by
  rw [tracePrefixInputs,traceNewInputs_weight,withNewOutputsFirst_weight]
  rfl

theorem physical_prefix_trace {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    tracePrefixInputs b hb (prefixChi b t) =
      ((outputDimension S (newOutputs b hb) : ℂ)⁻¹ •
        (1 : Mat (Registers S (newOutputs b hb)))) ⊗ₖ prefixChi (previousInput b hb) t := by
  unfold tracePrefixInputs prefixChi
  rw [traceNewInputs_chi,
    recorded_inputs_frozen S t _ _ (previous_time_le b hb)]
  have hf := fresh_selected_record S t (prefixCut (previousInput b hb))
    (arrived S (recordTime (previousInput b hb)))
    (released S (recordTime (previousInput b hb))) (released S (recordTime b))
    (previous_outputs_subset b hb) (new_outputs_active b hb)
  rw [prefixCut_time] at hf
  exact hf

/-- Tracing exactly the new input burst leaves the identity on the new
output ports tensored with the previous prefix, with no dimension scalar. -/
theorem higher_prefix_equation {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    tracePrefixInputs b hb (prefixGram b t) =
      (1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ prefixGram (previousInput b hb) t := by
  have hg (a : InputBurst S) : prefixGram a t =
      (prefixDimension a : ℂ) • prefixChi a t := gram_physical t _ _ _
  rw [hg b,tracePrefixInputs_weight,physical_prefix_trace,hg (previousInput b hb)]
  have hd : prefixDimension b = prefixDimension (previousInput b hb) *
      outputDimension S (newOutputs b hb) :=
    outputDimension_refinement S _ _ (previous_outputs_subset b hb)
  have hn : (outputDimension S (newOutputs b hb) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (outputDimension_pos S (newOutputs b hb))
  ext i j
  simp only [smul_apply,smul_eq_mul,kroneckerMap_apply]
  rw [hd,Nat.cast_mul]
  field_simp

theorem rank_zero_is_first {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (b : InputBurst S) (hb : (inputRank b).val = 0) : b = firstInputBurst S h := by
  apply le_antisymm
  · apply (inputEnumeration S).symm.le_iff_le.mp
    change (inputRank b).val ≤ (inputRank (firstInputBurst S h)).val
    omega
  · change (firstInputBurst S h).val.val.val ≤ b.val.val.val
    rw [firstInputBurst_start]
    omega

end History
end ScheduleLaw
