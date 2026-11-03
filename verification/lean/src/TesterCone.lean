import HigherPrefixes

/-! The positive causal-prefix feasible set. This module proves actual-tester
membership, the forced trace normalization, convexity and compactness. The
converse coherent realization is a separate proof obligation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw
namespace History

abbrev PrefixMatrices {I : Inventory} (S : Schedule I) :=
  (b : InputBurst S) → Mat (Record S (arrived S (recordTime b)) (released S (recordTime b)))

def IsCausalPrefixFamily {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S) : Prop :=
  (∀ b, (Z b).PosSemidef) ∧
    (∀ b, (inputRank b).val = 0 → partialLeft (Z b) = 1) ∧
    (∀ b (hb : 0 < (inputRank b).val), tracePrefixInputs b hb (Z b) =
      (1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ Z (previousInput b hb))

theorem actual_causal_prefix_family {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) :
    IsCausalPrefixFamily S (fun b => prefixGram b t) := by
  refine ⟨fun b => prefix_gram_positive b t,?_,fun b hb => higher_prefix_equation t b hb⟩
  intro b hb
  have hv : 0 < S.visits := by have := b.val.val.isLt; omega
  rw [rank_zero_is_first S hv b hb]
  exact first_prefix_equation S hv t

theorem tracePrefixInputs_trace {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (Z : Mat (Record S (arrived S (recordTime b))
      (released S (recordTime b)))) : (tracePrefixInputs b hb Z).trace = Z.trace := by
  unfold tracePrefixInputs withNewOutputsFirst traceNewInputs
  exact (submatrix_trace_equiv
    (outputRefinement S (arrived S (recordTime (previousInput b hb)))
      (released S (recordTime (previousInput b hb))) (released S (recordTime b))
      (previous_outputs_subset b hb)).symm _).trans
    ((partialRight_trace _).trans (submatrix_trace_equiv
      (inputRefinement S (arrived S (recordTime (previousInput b hb)))
        (arrived S (recordTime b)) (released S (recordTime b))
        (previous_inputs_subset b hb)).symm Z))

theorem prefix_dimension_step {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : prefixDimension b =
      prefixDimension (previousInput b hb) * outputDimension S (newOutputs b hb) :=
  outputDimension_refinement S _ _ (previous_outputs_subset b hb)

/-- Trace normalization follows from the operator-valued equations; it is
not imposed as an additional feasibility condition. -/
theorem causal_prefix_trace {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) : (Z b).trace = prefixDimension b := by
  have aux : ∀ k : ℕ, ∀ a : InputBurst S, (inputRank a).val = k →
      (Z a).trace = prefixDimension a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a ha
      by_cases hz : k = 0
      · have he := hZ.2.1 a (ha.trans hz)
        calc (Z a).trace = (partialLeft (Z a)).trace := (partialLeft_trace _).symm
          _ = (Fintype.card (OutputPrefix a) : ℂ) := by rw [he,trace_one]
          _ = prefixDimension a := by rw [registers_card]; rfl
      · have hp : 0 < (inputRank a).val := by omega
        have hr := previous_rank a hp
        have ht := ih (inputRank (previousInput a hp)).val (by omega) (previousInput a hp) rfl
        have he := congrArg Matrix.trace (hZ.2.2 a hp)
        rw [tracePrefixInputs_trace,trace_kronecker,trace_one,registers_card,ht] at he
        rw [he,prefix_dimension_step a hp,Nat.cast_mul,mul_comm]
  exact aux _ b rfl

theorem tracePrefixInputs_add {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (Z W : Mat (Record S (arrived S (recordTime b))
      (released S (recordTime b)))) :
    tracePrefixInputs b hb (Z+W) = tracePrefixInputs b hb Z + tracePrefixInputs b hb W := by
  ext i j
  simp only [tracePrefixInputs,withNewOutputsFirst,traceNewInputs,partialRight,
    submatrix_apply,add_apply,Finset.sum_add_distrib]

theorem partialLeft_additive {a b : Type} [Fintype a] (Z W : Mat (a × b)) :
    partialLeft (Z+W) = partialLeft Z + partialLeft W := by
  ext i j
  exact Finset.sum_add_distrib

theorem causal_prefix_convex {I : Inventory} (S : Schedule I) :
    Convex ℝ {Z : PrefixMatrices S | IsCausalPrefixFamily S Z} := by
  intro Z hZ W hW a b ha hb hab
  refine ⟨fun k => (hZ.1 k |>.smul ha).add (hW.1 k |>.smul hb),?_,?_⟩
  · intro k hk
    change partialLeft ((a : ℂ) • Z k + (b : ℂ) • W k) = 1
    rw [partialLeft_additive,ClassicalFlag.partialLeft_weight,
      ClassicalFlag.partialLeft_weight,hZ.2.1 k hk,hW.2.1 k hk,← add_smul]
    have hc : (a : ℂ)+(b : ℂ)=1 := by exact_mod_cast hab
    rw [hc,one_smul]
  · intro k hk
    change tracePrefixInputs k hk ((a : ℂ) • Z k + (b : ℂ) • W k) = _
    rw [tracePrefixInputs_add,tracePrefixInputs_weight,tracePrefixInputs_weight,
      hZ.2.2 k hk,hW.2.2 k hk]
    ext i j
    simp only [Pi.add_apply,Pi.smul_apply,smul_apply,smul_eq_mul,add_apply,kroneckerMap_apply,Complex.real_smul]
    ring

abbrev PrefixStates {I : Inventory} (S : Schedule I) :=
  (b : InputBurst S) → MState (Record S (arrived S (recordTime b)) (released S (recordTime b)))

def prefixFamilyOfStates {I : Inventory} (S : Schedule I) (ρ : PrefixStates S) : PrefixMatrices S :=
  fun b => (prefixDimension b : ℂ) • (ρ b).m

def causalStateSet {I : Inventory} (S : Schedule I) : Set (PrefixStates S) :=
  {ρ | (∀ b, (inputRank b).val = 0 → partialLeft (prefixFamilyOfStates S ρ b) = 1) ∧
    (∀ b (hb : 0 < (inputRank b).val), tracePrefixInputs b hb (prefixFamilyOfStates S ρ b) =
      (1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ prefixFamilyOfStates S ρ (previousInput b hb))}

theorem states_causal_iff {I : Inventory} (S : Schedule I) (ρ : PrefixStates S) :
    ρ ∈ causalStateSet S ↔ IsCausalPrefixFamily S (prefixFamilyOfStates S ρ) := by
  constructor
  · intro h
    refine ⟨?_,h⟩
    intro b
    exact (ρ b).psd.smul (show (0 : ℂ) ≤ (prefixDimension b : ℂ) by
      exact_mod_cast le_of_lt (outputDimension_pos S _))
  · exact fun h => h.2

theorem continuous_prefixFamilyOfStates {I : Inventory} (S : Schedule I) :
    Continuous (prefixFamilyOfStates S) := by
  apply continuous_pi
  intro b
  exact continuous_const.smul (MState.Continuous_Matrix.comp (continuous_apply b))

theorem continuous_partialLeft {a b : Type} [Fintype a] :
    Continuous (partialLeft (a := a) (b := b)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun Z : Mat (a × b) => ∑ k, Z (k,i) (k,j))
  fun_prop

theorem continuous_tracePrefixInputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : Continuous (tracePrefixInputs b hb) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold tracePrefixInputs withNewOutputsFirst traceNewInputs partialRight
  simp only [submatrix_apply]
  fun_prop

theorem isClosed_causalStateSet {I : Inventory} (S : Schedule I) : IsClosed (causalStateSet S) := by
  change IsClosed ({ρ : PrefixStates S | ∀ b, (inputRank b).val = 0 →
      partialLeft (prefixFamilyOfStates S ρ b) = 1} ∩
    {ρ : PrefixStates S | ∀ b (hb : 0 < (inputRank b).val),
      tracePrefixInputs b hb (prefixFamilyOfStates S ρ b) =
        (1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ
          prefixFamilyOfStates S ρ (previousInput b hb)})
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro b
    apply isClosed_iInter
    intro hb
    exact isClosed_eq (continuous_partialLeft.comp
      ((continuous_apply b).comp (continuous_prefixFamilyOfStates S))) continuous_const
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro b
    apply isClosed_iInter
    intro hb
    apply isClosed_eq ((continuous_tracePrefixInputs b hb).comp
      ((continuous_apply b).comp (continuous_prefixFamilyOfStates S)))
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun ρ => (1 : Mat (Registers S (newOutputs b hb))) i.1 j.1 *
      prefixFamilyOfStates S ρ (previousInput b hb) i.2 j.2)
    exact continuous_const.mul ((continuous_apply _).comp ((continuous_apply _).comp
      ((continuous_apply _).comp (continuous_prefixFamilyOfStates S))))

theorem isCompact_causalStateSet {I : Inventory} (S : Schedule I) : IsCompact (causalStateSet S) :=
  (isClosed_causalStateSet S).isCompact

def statesOfCausalFamily {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) : PrefixStates S := fun b =>
  (⟨(prefixDimension b : ℂ)⁻¹ • Z b,
      (hZ.1 b).smul (show (0 : ℂ) ≤ (prefixDimension b : ℂ)⁻¹ by
        exact inv_nonneg.mpr (by exact_mod_cast le_of_lt (outputDimension_pos S _))),by
      rw [trace_smul,causal_prefix_trace S Z hZ b,smul_eq_mul]
      exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt (outputDimension_pos S _))⟩ :
    Density (Record S (arrived S (recordTime b)) (released S (recordTime b)))).toMState

theorem statesOfCausalFamily_recover {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) : prefixFamilyOfStates S (statesOfCausalFamily S Z hZ) = Z := by
  funext b
  change (prefixDimension b : ℂ) • ((prefixDimension b : ℂ)⁻¹ • Z b) = Z b
  rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (outputDimension_pos S _)),one_smul]

theorem causal_prefix_set_eq_image {I : Inventory} (S : Schedule I) :
    {Z : PrefixMatrices S | IsCausalPrefixFamily S Z} = prefixFamilyOfStates S '' causalStateSet S := by
  ext Z
  constructor
  · intro hZ
    refine ⟨statesOfCausalFamily S Z hZ,?_,statesOfCausalFamily_recover S Z hZ⟩
    rw [states_causal_iff,statesOfCausalFamily_recover]
    exact hZ
  · rintro ⟨ρ,hρ,rfl⟩
    exact (states_causal_iff S ρ).mp hρ

/-- Compactness of the entire abstract feasible set, including zero visits.
This does not assert that its points have actual coherent tester realizations. -/
theorem isCompact_causal_prefix_set {I : Inventory} (S : Schedule I) :
    IsCompact {Z : PrefixMatrices S | IsCausalPrefixFamily S Z} := by
  rw [causal_prefix_set_eq_image]
  exact (isCompact_causalStateSet S).image (continuous_prefixFamilyOfStates S)

end History
end ScheduleLaw
