import BlueprintLocalPreparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def burstPreparationCut {I : Inventory} {S : Schedule I} (b : InputBurst S) : Cut S :=
  ⟨b.val.val.val,by have := b.val.val.isLt; omega⟩

theorem release_not_in_input_burst {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (v : Fin S.visits) : S.position (v,true) ∉ events b.val := by
  intro hv
  have hk := same_kind b.val (S.position (v,true)) hv
  rw [kind_endpoint,b.property] at hk
  contradiction

theorem input_release_after_burst {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (v : Fin S.visits) (hv : v ∈ inputVisits b) :
    (last b.val).val < (S.position (v,true)).val := by
  have hi := (mem_events_iff b.val _).mp (Finset.mem_filter.mp hv).2
  have hstart : b.val.val.val ≤ (S.position (v,false)).val := hi.1
  have ho := S.ordered v
  by_contra hn
  apply release_not_in_input_burst b v
  apply (mem_events_iff b.val _).mpr
  exact ⟨by change b.val.val.val ≤ _; change _ < _ at ho; omega,by simpa only [not_lt] using hn⟩

theorem inputVisits_active_at_prefix {I : Inventory} {S : Schedule I}
    (b : InputBurst S) : inputVisits b ⊆ activeVisits S (prefixCut b) := by
  intro v hv
  have hi := (mem_events_iff b.val _).mp (Finset.mem_filter.mp hv).2
  have hend : (S.position (v,false)).val ≤ (last b.val).val := hi.2
  have hr := input_release_after_burst b v hv
  simp only [activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,prefixCut]
  constructor <;> omega

theorem inputVisits_carriers_injective {I : Inventory} {S : Schedule I}
    (b : InputBurst S) : Set.InjOn S.carrier (inputVisits b : Set (Fin S.visits)) :=
  activeVisits_carriers_injective S (prefixCut b) (inputVisits b) (inputVisits_active_at_prefix b)

theorem input_carrier_unheld_at_preparation {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (v : Fin S.visits) (hv : v ∈ inputVisits b) :
    S.carrier v ∈ (held S (burstPreparationCut b))ᶜ := by
  have hi := (mem_events_iff b.val _).mp (Finset.mem_filter.mp hv).2
  have ha : b.val.val.val ≤ (S.position (v,false)).val := hi.1
  have hb : (S.position (v,false)).val ≤ (last b.val).val := hi.2
  rw [Finset.mem_compl]
  intro hh
  obtain ⟨w,hwc,hwA,hwR⟩ := (Finset.mem_filter.mp hh).2
  change (S.position (w,false)).val < b.val.val.val at hwA
  change b.val.val.val ≤ (S.position (w,true)).val at hwR
  have hne : w ≠ v := by intro he; subst w; omega
  rcases S.disjoint w v hne hwc with h | h
  · apply release_not_in_input_burst b w
    apply (mem_events_iff b.val _).mpr
    change (S.position (w,true)).val < (S.position (v,false)).val at h
    exact ⟨hwR,by change _ ≤ (last b.val).val; omega⟩
  · have ho := S.ordered v
    change (S.position (v,true)).val < (S.position (w,false)).val at h
    change (S.position (v,false)).val < (S.position (v,true)).val at ho
    omega

theorem new_output_carrier_unheld_at_preparation {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hbr : 0 < (inputRank b).val)
    (v : Fin S.visits) (hv : v ∈ newOutputs b hbr) :
    S.carrier v ∈ (held S (burstPreparationCut b))ᶜ := by
  have hvr := (released_at_record b v).mp (Finset.mem_sdiff.mp hv).1
  have hvp : recordTime (previousInput b hbr) ≤ (S.position (v,true)).val+1 := by
    have hp := (Finset.mem_sdiff.mp hv).2
    simpa only [released,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hp
  rw [Finset.mem_compl]
  intro hh
  obtain ⟨w,hwc,hwA,hwR⟩ := (Finset.mem_filter.mp hh).2
  change (S.position (w,false)).val < b.val.val.val at hwA
  change b.val.val.val ≤ (S.position (w,true)).val at hwR
  change (S.position (v,true)).val < b.val.val.val at hvr
  have hne : v ≠ w := by intro he; subst w; omega
  rcases S.disjoint v w hne hwc.symm with h | h
  · change (S.position (v,true)).val < (S.position (w,false)).val at h
    have hlast : b.val.val.val ≤ (last b.val).val := first_le_last b.val
    have hnew : w ∈ arrived S (recordTime b) \ arrived S (recordTime (previousInput b hbr)) := by
      simp only [Finset.mem_sdiff,arrived,Finset.mem_filter,Finset.mem_univ,true_and,recordTime]
      simp only [recordTime] at hvp
      constructor <;> omega
    rw [new_inputs_exact b hbr] at hnew
    have hw := (mem_events_iff b.val _).mp (Finset.mem_filter.mp hnew).2
    have hl : b.val.val.val ≤ (S.position (w,false)).val := hw.1
    omega
  · have ho := S.ordered v
    change (S.position (w,true)).val < (S.position (v,false)).val at h
    change (S.position (v,false)).val < (S.position (v,true)).val at ho
    omega

theorem earlier_recordTime_le_preparation {I : Inventory} {S : Schedule I}
    (a b : InputBurst S) (hab : a < b) : recordTime a ≤ (burstPreparationCut b).val := by
  have hl := burst_last_lt_first a.val b.val hab
  have hfalse := same_kind a.val (last a.val) (last_mem a.val)
  rw [a.property] at hfalse
  have hsep : (last a.val).val+1 ≠ b.val.val.val := by
    intro he
    have hp : 0 < b.val.val.val := by omega
    have hn := start_left_boundary S b.val.val.val b.val.property hp
    have hpred : b.val.val.val-1=(last a.val).val := by omega
    apply hn
    rw [hpred,b.property,hfalse]
  simp only [recordTime,burstPreparationCut]
  change (last a.val).val < b.val.val.val at hl
  omega

theorem postcomposeTester_earlier_prefix {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (b : InputBurst S)
    (U : Mat (Fin r × Restricted I (held S (burstPreparationCut b))ᶜ)) (hU : IsUnitary U)
    (a : InputBurst S) (hab : a < b) :
    prefixGram a (postcomposeTester t (burstPreparationCut b) U hU)=prefixGram a t :=
  postcomposeTester_prefixGram t _ U hU a (earlier_recordTime_le_preparation a b hab)

def restrictedCarrierPartition (I : Inventory) (A B : Finset (Fin I.count)) (hBA : B ⊆ A) :
    Restricted I A ≃ Restricted I B × Restricted I (A \ B) where
  toFun p := (fun c => p ⟨c.val,hBA c.property⟩,fun c => p ⟨c.val,(Finset.mem_sdiff.mp c.property).1⟩)
  invFun p c := if h : c.val ∈ B then p.1 ⟨c.val,h⟩ else p.2 ⟨c.val,Finset.mem_sdiff.mpr ⟨c.property,h⟩⟩
  left_inv p := by
    funext c
    by_cases hc : c.val ∈ B <;> simp [hc]
  right_inv p := by
    apply Prod.ext
    · funext c; simp [c.property]
    · funext c; simp [(Finset.mem_sdiff.mp c.property).2]

def localVisitPartition {I : Inventory} (S : Schedule I) (A : Finset (Fin I.count))
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (hVA : visitCarriers S V ⊆ A) :
    Restricted I A ≃ Registers S V × Restricted I (A \ visitCarriers S V) :=
  (restrictedCarrierPartition I A (visitCarriers S V) hVA).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun c : {c // c ∈ visitCarriers S V} => Fin (I.dim c.val))
        (carrierVisits S V hc)).symm (Equiv.refl _))

theorem input_carriers_available {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    visitCarriers S (inputVisits b) ⊆ (held S (burstPreparationCut b))ᶜ := by
  intro c hc
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
  exact input_carrier_unheld_at_preparation b v hv

theorem output_carriers_available {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    visitCarriers S (newOutputs b hb) ⊆ (held S (burstPreparationCut b))ᶜ := by
  intro c hc
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
  exact new_output_carrier_unheld_at_preparation b hb v hv

def localInputCoordinates {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    Restricted I (held S (burstPreparationCut b))ᶜ ≃ Registers S (inputVisits b) ×
      Restricted I ((held S (burstPreparationCut b))ᶜ \ visitCarriers S (inputVisits b)) :=
  localVisitPartition S _ (inputVisits b) (inputVisits_carriers_injective b) (input_carriers_available b)

def localOutputCoordinates {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    Restricted I (held S (burstPreparationCut b))ᶜ ≃ Registers S (newOutputs b hb) ×
      Restricted I ((held S (burstPreparationCut b))ᶜ \ visitCarriers S (newOutputs b hb)) :=
  localVisitPartition S _ (newOutputs b hb)
    (activeVisits_carriers_injective S _ _ (new_outputs_active b hb)) (output_carriers_available b hb)

end ScheduleLaw.Blueprint
