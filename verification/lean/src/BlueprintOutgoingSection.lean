import BlueprintOutgoingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem current_section_record {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    prefixStepCoordinates b hb (canonicalBoundaryCoordinates b
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z)))).1=
      ((burstPastRecord b hb c.1,burstOutputRecord b hb c.1),burstLocalInput b hb z) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · funext v
        change (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
          ((rawBurstCoordinates b).symm (c,z))).1.1 v.val=c.1.1 v.val
        apply gauge_preserves_input
        intro hv
        rw [←new_inputs_exact b hb] at hv
        exact (Finset.mem_sdiff.mp hv).2 v.property
      · funext v
        change (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
          ((rawBurstCoordinates b).symm (c,z))).1.2 v.val=c.1.2 v.val
        rw [gauge_preserves_partners]
        rfl
    · funext v
      change (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z))).1.2 v.val=c.1.2 v.val
      rw [gauge_preserves_partners]
      rfl
  · apply (burstInputPortCoordinates b hb).injective
    rw [burstLocalInput,Equiv.apply_symm_apply]
    funext v
    rw [burstInputPortCoordinates,registers_cast_apply]
    change (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
      ((rawBurstCoordinates b).symm (c,z))).1.1 v.val=
        z.2 ⟨S.carrier v.val,input_carrier_unheld_at_preparation b v.val v.property⟩
    rw [gauge_input_mem S _ _ _ v.val v.property]
    exact congrFun (rawBurstCoordinates_free b (c,z))
      ⟨S.carrier v.val,input_carrier_unheld_at_preparation b v.val v.property⟩
    all_goals exact new_inputs_exact b hb

theorem canonical_outgoing_section {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    canonicalPrefixVector Z hZ b
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z)))=
      burstCommonFactor b hb c *
        ∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (burstPastRecord b hb c.1,burstOutputRecord b hb c.1) a *
            burstOutgoingMatrix b hb z a := by
  classical
  have hr := (prefixStepCoordinates b hb).injective
    (current_section_record b hb c z |>.trans
      ((prefixStepCoordinates b hb).apply_symm_apply _).symm)
  rw [canonicalPrefixVector_formula,outgoing_record_sum]
  simp only [current_section_future]
  change (if (∀ v : {v // v∈(arrived S (recordTime b))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z))).2.1=
          prefixTailPayload b (fun v => (gauge S _ (inputVisits b)
            (inputVisits_carriers_injective b) ((rawBurstCoordinates b).symm (c,z))).1.2 v.val)
      then _ else 0)=_
  simp only [gauge_preserves_partners,hr,gauge_preserves_memory]
  change (if (∀ v : {v // v∈(arrived S (recordTime b))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z))).2.1=prefixTailPayload b (fun v => c.1.2 v.val)
      then canonicalRecordAmplitude Z hZ b
        ((prefixStepCoordinates b hb).symm
          ((burstPastRecord b hb c.1,burstOutputRecord b hb c.1),burstLocalInput b hb z)) z.1 else 0)=_
  simp only [current_section_payload b hb c z]
  have hcond : ((∀ v : {v // v∈(arrived S (recordTime b))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
      (c.2=restrictPayload I (held S (burstPreparationCut b))
        (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val)) ∧
      (∀ v : {v // v∈inputVisits b}, c.1.1 v.val=c.1.2 v.val) ∧
      (localInputCoordinates b z.2).2=(fun d => ⟨0,I.dim_pos d.val⟩))) ↔
      ((∀ v : {v // v∈(arrived S (recordTime (previousInput b hb)))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
        c.2=restrictPayload I (held S (burstPreparationCut b))
          (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val))) ∧
      (localInputCoordinates b z.2).2=(fun d => ⟨0,I.dim_pos d.val⟩) := by
    constructor
    · rintro ⟨hf,hh,hi,hz⟩
      exact ⟨⟨(future_inputs_split b hb c.1).mp ⟨hf,hi⟩,hh⟩,hz⟩
    · rintro ⟨⟨hf,hh⟩,hz⟩
      obtain ⟨hf,hi⟩ := (future_inputs_split b hb c.1).mpr hf
      exact ⟨hf,hh,hi,hz⟩
  simp only [hcond]
  unfold burstCommonFactor
  split_ifs <;> simp_all

end ScheduleLaw.Blueprint
