import BlueprintFirstTester

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def preparationLive {I : Inventory} {S : Schedule I} (b : InputBurst S) : Finset (Fin S.visits) :=
  activeVisits S (burstPreparationCut b)

theorem arrival_before_preparation_iff {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (v : Fin S.visits) :
    (S.position (v,false)).val<(burstPreparationCut b).val ↔
      v∈arrived S (recordTime (previousInput b hb)) := by
  constructor
  · intro hv
    have hs := start_le S (S.position (v,false)).val
    have hbefore : inputBurst v<b := by
      change start S (S.position (v,false)).val<b.val.val.val
      simp only [burstPreparationCut] at hv
      omega
    have hl := le_previous b hb (inputBurst v) hbefore
    have hpos := ((mem_events_iff (inputBurst v).val _).mp (burstOf_mem _)).2
    have hm := burst_last_mono (inputBurst v).val (previousInput b hb).val hl
    exact (arrived_at_record _ _).mpr (le_trans hpos hm)
  · intro hv
    have hp : (S.position (v,false)).val≤(last (previousInput b hb).val).val :=
      (arrived_at_record _ _).mp hv
    have hs : (last (previousInput b hb).val).val<b.val.val.val :=
      burst_last_lt_first _ _ (previous_lt b hb)
    exact lt_of_le_of_lt hp hs

theorem preparationLive_eq {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) :
    preparationLive b=arrived S (recordTime (previousInput b hb)) \ released S (recordTime b) := by
  ext v
  simp only [preparationLive,activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_sdiff,←arrival_before_preparation_iff b hb v,released_at_record]
  change (_ ∧ b.val.val.val≤(S.position (v,true)).val) ↔
    (_ ∧ ¬(S.position (v,true)).val<b.val.val.val)
  omega

theorem held_eq_active_carriers {I : Inventory} (S : Schedule I) (k : Cut S) :
    held S k=visitCarriers S (activeVisits S k) := by
  ext c
  simp only [held,visitCarriers,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,activeVisits]
  constructor
  · rintro ⟨v,hc,ha,hr⟩
    exact ⟨v,⟨ha,hr⟩,hc⟩
  · rintro ⟨v,hv,hc⟩
    obtain ⟨ha,hr⟩ := hv
    exact ⟨v,hc,ha,hr⟩

theorem previous_live_partition {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) :
    prefixLive (previousInput b hb)=preparationLive b∪newOutputs b hb := by
  rw [prefixLive_eq,preparationLive_eq b hb]
  ext v
  constructor
  · intro hv
    obtain ⟨ha,ho⟩ := Finset.mem_sdiff.mp hv
    by_cases hn : v∈released S (recordTime b)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hn,ho⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha,hn⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hp|hn
    · obtain ⟨ha,ho⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_sdiff.mpr ⟨ha,fun h => ho (previous_outputs_subset b hb h)⟩
    · exact Finset.mem_sdiff.mpr ⟨new_outputs_old_inputs b hb hn,(Finset.mem_sdiff.mp hn).2⟩

theorem current_live_partition {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) :
    prefixLive b=preparationLive b∪inputVisits b := by
  rw [prefixLive_eq,preparationLive_eq b hb]
  ext v
  constructor
  · intro hv
    obtain ⟨ha,ho⟩ := Finset.mem_sdiff.mp hv
    by_cases hp : v∈arrived S (recordTime (previousInput b hb))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,ho⟩)
    · apply Finset.mem_union_right
      rw [←new_inputs_exact b hb]
      exact Finset.mem_sdiff.mpr ⟨ha,hp⟩
  · intro hv
    rcases Finset.mem_union.mp hv with hp|hn
    · obtain ⟨ha,ho⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_sdiff.mpr ⟨previous_inputs_subset b hb ha,ho⟩
    · have hh := inputVisits_active_at_prefix b hn
      rw [←prefixLive_eq]
      exact hh

theorem previous_live_carriers {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) :
    visitCarriers S (prefixLive (previousInput b hb))=
      held S (burstPreparationCut b)∪visitCarriers S (newOutputs b hb) := by
  rw [previous_live_partition b hb,visitCarriers,Finset.image_union]
  rw [held_eq_active_carriers]
  rfl

theorem current_live_carriers {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) :
    visitCarriers S (prefixLive b)=
      held S (burstPreparationCut b)∪visitCarriers S (inputVisits b) := by
  rw [current_live_partition b hb,visitCarriers,Finset.image_union]
  rw [held_eq_active_carriers]
  rfl

theorem prefixTailPayload_held_agree {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (u : Recorder.Inputs S) (c : Fin I.count)
    (hc : c∈held S (burstPreparationCut b)) :
    prefixTailPayload (previousInput b hb) (fun v => u v.val) c=
      prefixTailPayload b (fun v => u v.val) c := by
  rw [held_eq_active_carriers] at hc
  obtain ⟨v,hv,hvc⟩ := Finset.mem_image.mp hc
  have hp : v∈prefixLive (previousInput b hb) := by
    rw [previous_live_partition b hb]
    exact Finset.mem_union_left _ hv
  have hn : v∈prefixLive b := by
    rw [current_live_partition b hb]
    exact Finset.mem_union_left _ hv
  subst c
  rw [prefixTailPayload_live _ _ ⟨v,hp⟩,prefixTailPayload_live _ _ ⟨v,hn⟩]

end ScheduleLaw.Blueprint
