import BlueprintBurstLocalAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem first_input_rank_zero {I : Inventory} {S : Schedule I} (h : 0<S.visits) :
    (inputRank (firstInputBurst S h)).val=0 := by
  by_contra hn
  have hp : 0<(inputRank (firstInputBurst S h)).val := Nat.pos_of_ne_zero hn
  have hl := previous_lt (firstInputBurst S h) hp
  change (previousInput (firstInputBurst S h) hp).val.val.val<0 at hl
  omega

theorem rank_zero_first {I : Inventory} {S : Schedule I} (h : 0<S.visits) (b : InputBurst S)
    (hb : (inputRank b).val=0) : b=firstInputBurst S h := by
  apply (inputEnumeration S).symm.injective
  exact Fin.ext (hb.trans (first_input_rank_zero h).symm)

theorem positive_after_first {I : Inventory} {S : Schedule I} (h : 0<S.visits)
    (b : InputBurst S) (hb : 0<(inputRank b).val) : firstInputBurst S h<b := by
  apply (inputEnumeration S).symm.strictMono.lt_iff_lt.mp
  change (inputRank (firstInputBurst S h)).val<(inputRank b).val
  rw [first_input_rank_zero h]
  exact hb

theorem scheduled_first_gates {I : Inventory} {S : Schedule I} (h : 0<S.visits)
    (t : Tester S (burstMemoryDim S))
    (hg : ∀ k : Cut S, (∀ a : InputBurst S, 0<(inputRank a).val → burstPreparationCut a≠k) → t.gate k=1)
    (k : Cut S) (hk : k.val<recordTime (firstInputBurst S h)) : t.gate k=1 := by
  apply hg
  intro a ha he
  have hl := earlier_recordTime_le_preparation (firstInputBurst S h) a (positive_after_first h a ha)
  have hv := congrArg Fin.val he
  omega

theorem scheduled_input_gates {I : Inventory} {S : Schedule I}
    (t : Tester S (burstMemoryDim S))
    (hg : ∀ k : Cut S, (∀ a : InputBurst S, 0<(inputRank a).val → burstPreparationCut a≠k) → t.gate k=1)
    (b : InputBurst S) (k : Cut S)
    (hs : (burstPreparationCut b).val+1≤k.val) (hf : k.val<recordTime b) : t.gate k=1 := by
  apply hg
  intro a ha he
  have hv := congrArg Fin.val he
  rcases lt_trichotomy a b with hab|hab|hba
  · have hl := burst_last_lt_first a.val b.val hab
    have hstart := first_le_last a.val
    change a.val.val.val≤(last a.val).val at hstart
    change (last a.val).val<b.val.val.val at hl
    simp only [burstPreparationCut] at hs hv
    omega
  · subst a
    omega
  · have hl := earlier_recordTime_le_preparation b a hba
    omega

theorem scheduled_gap_gates {I : Inventory} {S : Schedule I}
    (t : Tester S (burstMemoryDim S))
    (hg : ∀ k : Cut S, (∀ a : InputBurst S, 0<(inputRank a).val → burstPreparationCut a≠k) → t.gate k=1)
    (b : InputBurst S) (hb : 0<(inputRank b).val) (k : Cut S)
    (hs : recordTime (previousInput b hb)≤k.val) (hf : k.val<(burstPreparationCut b).val) : t.gate k=1 := by
  apply hg
  intro a ha he
  have hv := congrArg Fin.val he
  by_cases hab : a<b
  · have hl := burst_last_mono a.val (previousInput b hb).val (le_previous b hb a hab)
    have hstart := first_le_last a.val
    change a.val.val.val≤(last a.val).val at hstart
    change (last a.val).val≤(last (previousInput b hb).val).val at hl
    simp only [recordTime] at hs
    simp only [burstPreparationCut] at hv
    omega
  · have hl : b.val.val.val≤a.val.val.val := le_of_not_gt hab
    simp only [burstPreparationCut] at hf hv
    omega

theorem release_gap_execution {I : Inventory} {S : Schedule I}
    (t : Tester S (burstMemoryDim S)) (φ : Recorder.Stock S → ℂ)
    (hg : ∀ k : Cut S, (∀ a : InputBurst S, 0<(inputRank a).val → burstPreparationCut a≠k) → t.gate k=1)
    (b : InputBurst S) (hb : 0<(inputRank b).val) :
    amplitudes t φ (burstPreparationCut b).val=amplitudes t φ (recordTime (previousInput b hb)) := by
  let V : Finset (Fin S.visits) := ∅
  have hc : Set.InjOn S.carrier (V : Set (Fin S.visits)) := by
    intro v hv; simp [V] at hv
  have h := amplitudes_idle_gauge t φ V hc (recordTime (previousInput b hb)) (burstPreparationCut b).val
    (earlier_recordTime_le_preparation _ _ (previous_lt b hb)) (Nat.le_of_lt (burstPreparationCut b).isLt)
    (by simp [considered,V]) (scheduled_gap_gates t hg b hb) (by
      intro n hs hf v hv
      exact False.elim (release_gap_no_arrival b hb n hs (Nat.le_of_lt hf) v hv))
  have he : gaugeAt S (burstMemoryDim S) V hc (burstPreparationCut b).val=1 := by
    exact (gauge_congr S _ _ ∅ _ hc (by simp [considered,V])).trans (gauge_empty S _ hc)
  funext x
  simpa only [he,Equiv.Perm.one_apply] using h x

end ScheduleLaw.Blueprint
