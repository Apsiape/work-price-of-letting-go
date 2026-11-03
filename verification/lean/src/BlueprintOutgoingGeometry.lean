import BlueprintOutgoingSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem gauge_burst_held {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    restrictPayload I (held S (burstPreparationCut b))
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z))).2.1=c.2 := by
  rw [←rawBurstCoordinates_held b (c,z)]
  funext d
  apply gauge_preserves_carrier
  intro v hv he
  exact Finset.mem_compl.mp (input_carriers_available b (Finset.mem_image.mpr ⟨v,hv,he.symm⟩)) d.property

theorem gauge_burst_free_inputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (localInputCoordinates b (restrictPayload I (held S (burstPreparationCut b))ᶜ
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z))).2.1)).1=(fun v : {v // v∈inputVisits b} => c.1.1 v.val) := by
  funext v
  exact gauge_payload_mem S _ (inputVisits b) (inputVisits_carriers_injective b) v.val v.property _

theorem gauge_burst_free_rest {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (localInputCoordinates b (restrictPayload I (held S (burstPreparationCut b))ᶜ
      (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
        ((rawBurstCoordinates b).symm (c,z))).2.1)).2=(localInputCoordinates b z.2).2 := by
  funext d
  have hg := gauge_preserves_carrier S (burstMemoryDim S) (inputVisits b)
    (inputVisits_carriers_injective b) d.val (by
      intro v hv he
      exact (Finset.mem_sdiff.mp d.property).2 (Finset.mem_image.mpr ⟨v,hv,he.symm⟩))
    ((rawBurstCoordinates b).symm (c,z))
  have hr := congrFun (rawBurstCoordinates_free b (c,z))
    ⟨d.val,(Finset.mem_sdiff.mp d.property).1⟩
  exact hg.trans hr

theorem current_section_payload {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
      ((rawBurstCoordinates b).symm (c,z))).2.1=prefixTailPayload b (fun v => c.1.2 v.val) ↔
      c.2=restrictPayload I (held S (burstPreparationCut b))
        (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val)) ∧
      (∀ v : {v // v∈inputVisits b}, c.1.1 v.val=c.1.2 v.val) ∧
      (localInputCoordinates b z.2).2=(fun d => ⟨0,I.dim_pos d.val⟩) := by
  have hh : restrictPayload I (held S (burstPreparationCut b)) (prefixTailPayload b (fun v => c.1.2 v.val))=
      restrictPayload I (held S (burstPreparationCut b))
        (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val)) := by
    funext d
    exact (prefixTailPayload_held_agree b hb c.1.2 d.val d.property).symm
  rw [payload_eq_restrictions I (held S (burstPreparationCut b)),gauge_burst_held,hh,
    currentTail_free_port b hb c.1.2,Equiv.eq_symm_apply,Prod.ext_iff,
    gauge_burst_free_inputs,gauge_burst_free_rest]
  exact and_congr_right (fun _ => and_congr_left (fun _ => funext_iff))

theorem current_section_future {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (canonicalBoundaryCoordinates b (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
      ((rawBurstCoordinates b).symm (c,z)))).2.1.1=
      prefixTailInputs b (canonicalBoundaryCoordinates b
        (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
          ((rawBurstCoordinates b).symm (c,z)))).2.1.2 ↔
      ∀ v : {v // v∈(arrived S (recordTime b))ᶜ}, c.1.1 v.val=c.1.2 v.val := by
  have hi (v : {v // v∈(arrived S (recordTime b))ᶜ}) : v.val∉inputVisits b := by
    intro hv
    have hl := inputVisits_active_at_prefix b hv
    change v.val∈prefixLive b at hl
    rw [prefixLive_eq] at hl
    exact Finset.mem_compl.mp v.property (Finset.mem_sdiff.mp hl).1
  constructor
  · intro h v
    have he := congrFun h v
    change (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
      ((rawBurstCoordinates b).symm (c,z))).1.1 v.val=
        (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
          ((rawBurstCoordinates b).symm (c,z))).1.2 v.val at he
    rw [gauge_preserves_input S _ _ _ v.val (hi v),gauge_preserves_partners] at he
    exact he
  · intro h
    funext v
    change (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
      ((rawBurstCoordinates b).symm (c,z))).1.1 v.val=
        (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
          ((rawBurstCoordinates b).symm (c,z))).1.2 v.val
    rw [gauge_preserves_input S _ _ _ v.val (hi v),gauge_preserves_partners]
    exact h v

theorem future_inputs_split {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (s : Recorder.Stock S) :
    (∀ v : {v // v∈(arrived S (recordTime b))ᶜ}, s.1 v.val=s.2 v.val) ∧
      (∀ v : {v // v∈inputVisits b}, s.1 v.val=s.2 v.val) ↔
      ∀ v : {v // v∈(arrived S (recordTime (previousInput b hb)))ᶜ}, s.1 v.val=s.2 v.val := by
  constructor
  · rintro ⟨hf,hi⟩ v
    by_cases hv : v.val∈arrived S (recordTime b)
    · apply hi ⟨v.val,?_⟩
      rw [←new_inputs_exact b hb]
      exact Finset.mem_sdiff.mpr ⟨hv,Finset.mem_compl.mp v.property⟩
    · exact hf ⟨v.val,Finset.mem_compl.mpr hv⟩
  · intro h
    constructor
    · intro v
      exact h ⟨v.val,Finset.mem_compl.mpr (fun hv =>
        Finset.mem_compl.mp v.property (previous_inputs_subset b hb hv))⟩
    · intro v
      have hv := v.property
      simp only [←new_inputs_exact b hb] at hv
      exact h ⟨v.val,Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2⟩

end ScheduleLaw.Blueprint
