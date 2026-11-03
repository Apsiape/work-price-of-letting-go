import PrefixPurification

/-! The paper's two-purification isometry step, now specialized to the exact
IsCausalPrefixFamily matrices and their actual burst reindexing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

abbrev PrefixSpace {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  Record S (arrived S (recordTime b)) (released S (recordTime b))

abbrev BurstInputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :=
  Registers S (arrived S (recordTime b) \ arrived S (recordTime (previousInput b hb)))

abbrev BurstOutputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) := Registers S (newOutputs b hb)

def prefixStepCoordinates {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    PrefixSpace b ≃ (PrefixSpace (previousInput b hb) × BurstOutputs b hb) × BurstInputs b hb :=
  (inputRefinement S (arrived S (recordTime (previousInput b hb)))
    (arrived S (recordTime b)) (released S (recordTime b)) (previous_inputs_subset b hb)).trans
    (Equiv.prodCongr
      ((outputRefinement S (arrived S (recordTime (previousInput b hb)))
        (released S (recordTime (previousInput b hb))) (released S (recordTime b))
        (previous_outputs_subset b hb)).trans (Equiv.prodComm _ _)) (Equiv.refl _))

def previousPrefixAmplitude {I : Inventory} {S : Schedule I} (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    Matrix (PrefixSpace (previousInput b hb)) (PrefixSpace (previousInput b hb)) ℂ :=
  fun x m => prefixPurification S Z hZ (previousInput b hb) (x,m)

def currentPrefixAmplitude {I : Inventory} {S : Schedule I} (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    Matrix (PrefixSpace (previousInput b hb) × BurstOutputs b hb)
      (BurstInputs b hb × PrefixSpace b) ℂ :=
  fun x k => prefixPurification S Z hZ b ((prefixStepCoordinates b hb).symm (x,k.1),k.2)

theorem prefixStep_trace_entry {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (Z : Mat (PrefixSpace b))
    (x y : PrefixSpace (previousInput b hb)) (z z' : BurstOutputs b hb) :
    (∑ i : BurstInputs b hb, Z ((prefixStepCoordinates b hb).symm ((x,z),i))
      ((prefixStepCoordinates b hb).symm ((y,z'),i))) =
        tracePrefixInputs b hb Z (z,x) (z',y) := rfl

/-- The causal operator equation is exactly the equality of the two
purification Gram matrices required by the isometry construction. -/
theorem prefix_purifications_equal_gram {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (x y : PrefixSpace (previousInput b hb))
    (z z' : BurstOutputs b hb) :
    (∑ i,∑ k, currentPrefixAmplitude Z hZ b hb (x,z) (i,k) *
      star (currentPrefixAmplitude Z hZ b hb (y,z') (i,k))) =
      if z = z' then ∑ m, previousPrefixAmplitude Z hZ b hb x m *
        star (previousPrefixAmplitude Z hZ b hb y m) else 0 := by
  have he : (∑ i,∑ k, currentPrefixAmplitude Z hZ b hb (x,z) (i,k) *
      star (currentPrefixAmplitude Z hZ b hb (y,z') (i,k))) =
        tracePrefixInputs b hb (Z b) (z,x) (z',y) := by
    rw [← prefixStep_trace_entry]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrFun₂ (prefixPurification_gram S Z hZ b)
      ((prefixStepCoordinates b hb).symm ((x,z),i))
      ((prefixStepCoordinates b hb).symm ((y,z'),i))
  rw [he,hZ.2.2 b hb]
  have hp := congrFun₂ (prefixPurification_gram S Z hZ (previousInput b hb)) x y
  change (∑ m, previousPrefixAmplitude Z hZ b hb x m *
    star (previousPrefixAmplitude Z hZ b hb y m)) = Z (previousInput b hb) x y at hp
  rw [hp]
  simp only [kroneckerMap_apply,one_apply]
  by_cases h : z = z' <;> simp [h]

/-- A full-domain, waste-retaining isometry at every higher burst. No
faithfulness assumption and no CombRealization argument is used. -/
theorem canonical_prefix_burst_isometry {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    ∃ V : Matrix (BurstInputs b hb × (PrefixSpace b ⊕
        (PrefixSpace (previousInput b hb) × BurstOutputs b hb)))
      (PrefixSpace (previousInput b hb) × BurstOutputs b hb) ℂ,
      Vᴴ * V = 1 ∧ ∀ x z i k,
        paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (x,z) (i,k) =
            ∑ m, previousPrefixAmplitude Z hZ b hb x m * V (i,k) (m,z) :=
  exists_padded_burst_isometry (previousPrefixAmplitude Z hZ b hb)
    (currentPrefixAmplitude Z hZ b hb) (prefix_purifications_equal_gram Z hZ b hb)

end ScheduleLaw.History
