import BlueprintBoundarySections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem payload_eq_restrictions (I : Inventory) (A : Finset (Fin I.count)) (p q : Payload I) :
    p=q ↔ restrictPayload I A p=restrictPayload I A q ∧
      restrictPayload I Aᶜ p=restrictPayload I Aᶜ q := by
  rw [←(payloadPartition I A).injective.eq_iff,Prod.ext_iff]
  rfl

theorem previous_section_payload {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    ((rawBurstCoordinates b).symm (c,z)).2.1=
      prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val) ↔
      c.2=restrictPayload I (held S (burstPreparationCut b))
        (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val)) ∧
      (localOutputCoordinates b hb z.2).1=burstOutputRecord b hb c.1 ∧
      (localOutputCoordinates b hb z.2).2=(fun d => ⟨0,I.dim_pos d.val⟩) := by
  rw [payload_eq_restrictions I (held S (burstPreparationCut b)),
    rawBurstCoordinates_held,rawBurstCoordinates_free,previousTail_free_port b hb c.1.2,
    Equiv.eq_symm_apply,Prod.ext_iff]
  rfl

/-- The actual accessible section of the previous canonical vector is
exactly the incoming port matrix used by the square burst gate. -/
theorem canonical_incoming_section {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    canonicalPrefixVector Z hZ (previousInput b hb) ((rawBurstCoordinates b).symm (c,z))=
      burstCommonFactor b hb c *
        ∑ m, previousPrefixAmplitude Z hZ b hb (burstPastRecord b hb c.1) m*
          burstIncomingMatrix b hb z (m,burstOutputRecord b hb c.1) := by
  classical
  have hf : (canonicalBoundaryCoordinates (previousInput b hb)
        ((rawBurstCoordinates b).symm (c,z))).2.1.1=
      prefixTailInputs (previousInput b hb) (canonicalBoundaryCoordinates (previousInput b hb)
        ((rawBurstCoordinates b).symm (c,z))).2.1.2 ↔
      ∀ v : {v // v∈(arrived S (recordTime (previousInput b hb)))ᶜ}, c.1.1 v.val=c.1.2 v.val := by
    constructor
    · intro h v
      exact congrFun h v
    · exact funext
  rw [canonicalPrefixVector_formula,incoming_record_sum]
  simp only [hf]
  change (if (∀ v : {v // v∈(arrived S (recordTime (previousInput b hb)))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
      ((rawBurstCoordinates b).symm (c,z)).2.1=
        prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val) then _ else 0)=_
  simp only [previous_section_payload b hb c z]
  change (if (∀ v : {v // v∈(arrived S (recordTime (previousInput b hb)))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
      (c.2=restrictPayload I (held S (burstPreparationCut b))
        (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val)) ∧
      (localOutputCoordinates b hb z.2).1=burstOutputRecord b hb c.1 ∧
      (localOutputCoordinates b hb z.2).2=(fun d => ⟨0,I.dim_pos d.val⟩)) then _ else 0)=_
  unfold burstCommonFactor
  split_ifs <;> simp_all <;> rfl

end ScheduleLaw.Blueprint
