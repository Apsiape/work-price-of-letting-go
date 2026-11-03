import HeldSchedule
import Mathlib.Data.Finset.Sort

/-! Consecutive input bursts, their prefix inclusions, and the fresh visits
between successive input boundaries. Bursts and ports remain visit indexed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def inputEnumeration {I : Inventory} (S : Schedule I) :
    Fin (Fintype.card (InputBurst S)) ≃o InputBurst S :=
  Fintype.orderIsoFinOfCardEq _ rfl

def inputRank {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    Fin (Fintype.card (InputBurst S)) := (inputEnumeration S).symm b

def previousInput {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : InputBurst S :=
  inputEnumeration S ⟨(inputRank b).val-1,by have := (inputRank b).isLt; omega⟩

theorem previous_rank {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    (inputRank (previousInput b hb)).val+1 = (inputRank b).val := by
  simp only [inputRank,previousInput,OrderIso.symm_apply_apply]
  simp only [inputRank] at hb
  omega

theorem previous_lt {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : previousInput b hb < b := by
  apply (inputEnumeration S).symm.strictMono.lt_iff_lt.mp
  change (inputRank (previousInput b hb)).val < (inputRank b).val
  have := previous_rank b hb
  omega

theorem le_previous {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (a : InputBurst S) (ha : a < b) :
    a ≤ previousInput b hb := by
  apply (inputEnumeration S).symm.le_iff_le.mp
  have hl := (inputEnumeration S).symm.strictMono ha
  change (inputRank a).val ≤ (inputRank (previousInput b hb)).val
  change (inputRank a).val < (inputRank b).val at hl
  have := previous_rank b hb
  omega

theorem no_input_between {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    ¬ ∃ a : InputBurst S, previousInput b hb < a ∧ a < b := by
  rintro ⟨a,ha,hab⟩
  exact (not_lt_of_ge (le_previous b hb a hab)) ha

theorem burst_last_lt_first {I : Inventory} {S : Schedule I} (a b : Burst S) (hab : a < b) :
    last a < b.val := by
  by_contra hn
  have hm : b.val ∈ events a := (mem_events_iff a _).mpr
    ⟨le_of_lt hab,le_of_not_gt hn⟩
  have hs := (Finset.mem_filter.mp hm).2
  rw [b.property] at hs
  have he : a = b := Subtype.ext (Fin.ext hs.symm)
  exact (ne_of_lt hab) he

theorem burst_last_mono {I : Inventory} {S : Schedule I} (a b : Burst S) (hab : a ≤ b) :
    last a ≤ last b := by
  rcases lt_or_eq_of_le hab with hl | rfl
  · exact (le_of_lt (burst_last_lt_first a b hl)).trans (first_le_last b)
  · rfl

theorem recordTime_strictMono {I : Inventory} (S : Schedule I) :
    StrictMono (recordTime (S := S)) := by
  intro a b hab
  have hl := burst_last_lt_first a.val b.val hab
  have hr := first_le_last b.val
  simp only [recordTime]
  change (last a.val).val < b.val.val.val at hl
  change b.val.val.val ≤ (last b.val).val at hr
  omega

theorem arrived_mono {I : Inventory} (S : Schedule I) {m n : ℕ} (hmn : m ≤ n) :
    arrived S m ⊆ arrived S n := by
  intro v hv
  simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
  omega

theorem released_mono {I : Inventory} (S : Schedule I) {m n : ℕ} (hmn : m ≤ n) :
    released S m ⊆ released S n := by
  intro v hv
  simp only [released,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
  omega

theorem previous_time_le {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : recordTime (previousInput b hb) ≤ recordTime b :=
  le_of_lt (recordTime_strictMono S (previous_lt b hb))

theorem previous_inputs_subset {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    arrived S (recordTime (previousInput b hb)) ⊆ arrived S (recordTime b) :=
  arrived_mono S (previous_time_le b hb)

theorem previous_outputs_subset {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    released S (recordTime (previousInput b hb)) ⊆ released S (recordTime b) :=
  released_mono S (previous_time_le b hb)

def prefixCut {I : Inventory} {S : Schedule I} (b : InputBurst S) : Cut S :=
  ⟨(last b.val).val+1,by have := input_last_not_terminal b; omega⟩

theorem prefixCut_time {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    (prefixCut b).val+1 = recordTime b := rfl

theorem inputBurst_le_of_arrival_le {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (b : InputBurst S) (hv : S.position (v,false) ≤ last b.val) : inputBurst v ≤ b := by
  have hs := start_mono S (show (S.position (v,false)).val ≤ (last b.val).val from hv)
  rw [last_start] at hs
  exact hs

theorem new_inputs_exact {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    arrived S (recordTime b) \ arrived S (recordTime (previousInput b hb)) = inputVisits b := by
  ext v
  simp only [Finset.mem_sdiff,arrived_at_record,input_visit_partition]
  constructor
  · rintro ⟨hv,hp⟩
    apply le_antisymm (inputBurst_le_of_arrival_le v b hv)
    by_contra hn
    have hl : inputBurst v < b := lt_of_not_ge hn
    have hle := le_previous b hb (inputBurst v) hl
    have he := ((mem_events_iff (inputBurst v).val _).mp (burstOf_mem _)).2
    exact hp (he.trans (burst_last_mono _ _ hle))
  · intro he
    have hm := (mem_events_iff b.val _).mp ((burstOf_unique _ b.val).mpr (congrArg Subtype.val he))
    refine ⟨hm.2,?_⟩
    have hl := burst_last_lt_first (previousInput b hb).val b.val (previous_lt b hb)
    exact not_le_of_gt (hl.trans_le hm.1)

def newOutputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) : Finset (Fin S.visits) :=
  released S (recordTime b) \ released S (recordTime (previousInput b hb))

/-- Every newly opened output is still held at the previous input boundary.
In particular, a newly loaned-and-returned wire cannot occur in this gap. -/
theorem new_outputs_active {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    newOutputs b hb ⊆ activeVisits S (prefixCut (previousInput b hb)) := by
  intro v hv
  obtain ⟨hr,hp⟩ := Finset.mem_sdiff.mp hv
  rw [released_at_record] at hr
  have hpri : (S.position (v,true)).val+1 ≥ recordTime (previousInput b hb) := by
    simpa only [released,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hp
  have ha := S.ordered v
  have hs := start_le S (S.position (v,false)).val
  have hl : inputBurst v < b := by
    change start S (S.position (v,false)).val < b.val.val.val
    change (S.position (v,false)).val < (S.position (v,true)).val at ha
    change (S.position (v,true)).val < b.val.val.val at hr
    omega
  have hle := le_previous b hb (inputBurst v) hl
  have he := ((mem_events_iff (inputBurst v).val _).mp (burstOf_mem _)).2
  have he' := he.trans (burst_last_mono _ _ hle)
  simp only [activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,prefixCut,recordTime] at hpri ⊢
  change (S.position (v,false)).val ≤ (last (previousInput b hb).val).val at he'
  omega

theorem new_outputs_old_inputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) :
    newOutputs b hb ⊆ arrived S (recordTime (previousInput b hb)) := by
  intro v hv
  have ha := (Finset.mem_filter.mp (new_outputs_active b hb hv)).2.1
  simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and,recordTime,prefixCut] at ha ⊢
  omega

end History
end ScheduleLaw
