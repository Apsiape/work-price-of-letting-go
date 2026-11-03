import RecorderSchedule

/-! Maximal monochromatic event bursts and visit-indexed history spaces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

abbrev Event {I : Inventory} (S : Schedule I) := Fin (2*S.visits)

/-- False is arrival, true is release. The value outside the event interval
only totalizes the recursion below and is never treated as a physical event. -/
def kind {I : Inventory} (S : Schedule I) (n : ℕ) : Bool :=
  if h : n < 2*S.visits then (S.position.symm ⟨n,h⟩).2 else false

theorem kind_endpoint {I : Inventory} (S : Schedule I) (v : Fin S.visits) (o : Bool) :
    kind S (S.position (v,o)).val = o := by
  simp [kind,(S.position (v,o)).isLt]

def start {I : Inventory} (S : Schedule I) : ℕ → ℕ
  | 0 => 0
  | n+1 => if kind S (n+1) = kind S n then start S n else n+1

theorem start_le {I : Inventory} (S : Schedule I) (n : ℕ) : start S n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [start]; split_ifs <;> omega

theorem start_step_mono {I : Inventory} (S : Schedule I) (n : ℕ) :
    start S n ≤ start S (n+1) := by
  simp only [start]
  split_ifs
  · exact le_rfl
  · exact (start_le S n).trans (Nat.le_succ n)

theorem start_mono {I : Inventory} (S : Schedule I) : Monotone (start S) :=
  monotone_nat_of_le_succ (start_step_mono S)

theorem start_idempotent {I : Inventory} (S : Schedule I) (n : ℕ) :
    start S (start S n) = start S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : kind S (n+1) = kind S n
    · simpa only [start,if_pos h] using ih
    · simp only [start,if_neg h]

theorem start_kind {I : Inventory} (S : Schedule I) (n : ℕ) :
    kind S (start S n) = kind S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : kind S (n+1) = kind S n
    · simpa only [start,if_pos h,h] using ih
    · simp only [start,if_neg h]

theorem start_interval {I : Inventory} (S : Schedule I) (n m : ℕ)
    (hm : start S n ≤ m) (hmn : m ≤ n) : start S m = start S n := by
  have h1 := start_mono S hm
  have h2 := start_mono S hmn
  rw [start_idempotent] at h1
  omega

theorem start_left_boundary {I : Inventory} (S : Schedule I) (n : ℕ)
    (hn : start S n = n) (hpos : 0 < n) : kind S n ≠ kind S (n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
  intro he
  change kind S (m+1) = kind S m at he
  rw [start,if_pos he] at hn
  have := start_le S m
  omega

/-- A burst is identified by its first actual endpoint, not by a carrier. -/
abbrev Burst {I : Inventory} (S : Schedule I) := {e : Event S // start S e.val = e.val}

def burstOf {I : Inventory} {S : Schedule I} (e : Event S) : Burst S :=
  ⟨⟨start S e.val,lt_of_le_of_lt (start_le S e.val) e.isLt⟩,start_idempotent S e.val⟩

def events {I : Inventory} {S : Schedule I} (b : Burst S) : Finset (Event S) :=
  Finset.univ.filter fun e => start S e.val = b.val.val

theorem first_mem {I : Inventory} {S : Schedule I} (b : Burst S) : b.val ∈ events b := by
  simp [events,b.property]

def last {I : Inventory} {S : Schedule I} (b : Burst S) : Event S :=
  (events b).max' ⟨b.val,first_mem b⟩

theorem last_mem {I : Inventory} {S : Schedule I} (b : Burst S) : last b ∈ events b :=
  Finset.max'_mem _ _

theorem first_le_last {I : Inventory} {S : Schedule I} (b : Burst S) : b.val ≤ last b :=
  Finset.le_max' _ _ (first_mem b)

theorem last_start {I : Inventory} {S : Schedule I} (b : Burst S) :
    start S (last b).val = b.val.val := by
  simpa only [events,Finset.mem_filter,Finset.mem_univ,true_and] using last_mem b

theorem mem_events_iff {I : Inventory} {S : Schedule I} (b : Burst S) (e : Event S) :
    e ∈ events b ↔ b.val ≤ e ∧ e ≤ last b := by
  constructor
  · intro he
    have hs : start S e.val = b.val.val := (Finset.mem_filter.mp he).2
    exact ⟨by have := start_le S e.val; change b.val.val ≤ e.val; omega,
      Finset.le_max' _ _ he⟩
  · rintro ⟨hl,hr⟩
    have he := start_interval S (last b).val e.val (by simpa only [last_start] using hl) hr
    simp only [events,Finset.mem_filter,Finset.mem_univ,true_and]
    exact he.trans (last_start b)

theorem same_kind {I : Inventory} {S : Schedule I} (b : Burst S) (e : Event S)
    (he : e ∈ events b) : kind S e.val = kind S b.val.val := by
  have hs := (Finset.mem_filter.mp he).2
  exact (start_kind S e.val).symm.trans (congrArg (kind S) hs)

theorem burstOf_mem {I : Inventory} {S : Schedule I} (e : Event S) : e ∈ events (burstOf e) := by
  simp [events,burstOf]

theorem burstOf_unique {I : Inventory} {S : Schedule I} (e : Event S) (b : Burst S) :
    e ∈ events b ↔ burstOf e = b := by
  simp only [events,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro he
    apply Subtype.ext
    exact Fin.ext he
  · intro he
    exact congrArg (fun b : Burst S => b.val.val) he

theorem right_boundary {I : Inventory} {S : Schedule I} (b : Burst S)
    (hn : (last b).val+1 < 2*S.visits) :
    kind S ((last b).val+1) ≠ kind S (last b).val := by
  intro he
  have hs : start S ((last b).val+1) = b.val.val := by rw [start,if_pos he,last_start]
  have hm : (⟨(last b).val+1,hn⟩ : Event S) ∈ events b := by simp [events,hs]
  have hb := (mem_events_iff b _).mp hm
  have := hb.2
  change (last b).val+1 ≤ (last b).val at this
  omega

abbrev InputBurst {I : Inventory} (S : Schedule I) := {b : Burst S // kind S b.val.val = false}
abbrev OutputBurst {I : Inventory} (S : Schedule I) := {b : Burst S // kind S b.val.val = true}

def inputBurst {I : Inventory} {S : Schedule I} (v : Fin S.visits) : InputBurst S :=
  ⟨burstOf (S.position (v,false)),by
    change kind S (start S (S.position (v,false)).val) = false
    rw [start_kind,kind_endpoint]⟩

def outputBurst {I : Inventory} {S : Schedule I} (v : Fin S.visits) : OutputBurst S :=
  ⟨burstOf (S.position (v,true)),by
    change kind S (start S (S.position (v,true)).val) = true
    rw [start_kind,kind_endpoint]⟩

def inputVisits {I : Inventory} {S : Schedule I} (b : InputBurst S) : Finset (Fin S.visits) :=
  Finset.univ.filter fun v => S.position (v,false) ∈ events b.val

def outputVisits {I : Inventory} {S : Schedule I} (b : OutputBurst S) : Finset (Fin S.visits) :=
  Finset.univ.filter fun v => S.position (v,true) ∈ events b.val

theorem input_visit_partition {I : Inventory} {S : Schedule I} (v : Fin S.visits) (b : InputBurst S) :
    v ∈ inputVisits b ↔ inputBurst v = b := by
  simp only [inputVisits,Finset.mem_filter,Finset.mem_univ,true_and,burstOf_unique]
  change (inputBurst v).val = b.val ↔ inputBurst v = b
  exact Subtype.ext_iff.symm

theorem output_visit_partition {I : Inventory} {S : Schedule I} (v : Fin S.visits) (b : OutputBurst S) :
    v ∈ outputVisits b ↔ outputBurst v = b := by
  simp only [outputVisits,Finset.mem_filter,Finset.mem_univ,true_and,burstOf_unique]
  change (outputBurst v).val = b.val ↔ outputBurst v = b
  exact Subtype.ext_iff.symm

def arrived {I : Inventory} (S : Schedule I) (n : ℕ) : Finset (Fin S.visits) :=
  Finset.univ.filter fun v => (S.position (v,false)).val+1 < n

def released {I : Inventory} (S : Schedule I) (n : ℕ) : Finset (Fin S.visits) :=
  Finset.univ.filter fun v => (S.position (v,true)).val+1 < n

/-- The state after the last arrival SWAP and before the first release event
of the next output burst. n counts cuts, in the existing run convention. -/
def recordTime {I : Inventory} {S : Schedule I} (b : InputBurst S) : ℕ := (last b.val).val+2

theorem input_last_not_terminal {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    (last b.val).val+1 < 2*S.visits := by
  have hk := same_kind b.val (last b.val) (last_mem b.val)
  rw [b.property] at hk
  let v := (S.position.symm (last b.val)).1
  have he : S.position (v,false) = last b.val := by
    apply S.position.symm.injective
    rw [Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · simpa only [kind,dif_pos (last b.val).isLt] using hk.symm
  have hv := S.ordered v
  rw [he] at hv
  have hb := (S.position (v,true)).isLt
  omega

theorem recordTime_bound {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    recordTime b ≤ 2*S.visits+1 := by
  have := input_last_not_terminal b
  simp only [recordTime]
  omega

theorem arrived_at_record {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (v : Fin S.visits) :
    v ∈ arrived S (recordTime b) ↔ (S.position (v,false)) ≤ last b.val := by
  simp only [arrived,recordTime,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

theorem released_at_record {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (v : Fin S.visits) :
    v ∈ released S (recordTime b) ↔ (S.position (v,true)) < b.val.val := by
  simp only [released,recordTime,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hv
    by_contra h
    have hr : S.position (v,true) ∈ events b.val :=
      (mem_events_iff b.val _).mpr ⟨le_of_not_gt h,by change _ ≤ (last b.val).val; omega⟩
    have hk := same_kind b.val _ hr
    rw [kind_endpoint,b.property] at hk
    contradiction
  · intro hv
    have := first_le_last b.val
    change (S.position (v,true)).val < b.val.val.val at hv
    change b.val.val.val ≤ (last b.val).val at this
    omega

abbrev InputPort {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  (v : {v // v ∈ inputVisits b}) → Fin (I.dim (S.carrier v.val))
abbrev OutputPort {I : Inventory} {S : Schedule I} (b : OutputBurst S) :=
  (v : {v // v ∈ outputVisits b}) → Fin (I.dim (S.carrier v.val))
abbrev InputPrefix {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  (v : {v // v ∈ arrived S (recordTime b)}) → Fin (I.dim (S.carrier v.val))
abbrev OutputPrefix {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  (v : {v // v ∈ released S (recordTime b)}) → Fin (I.dim (S.carrier v.val))

theorem bursts_empty_of_zero {I : Inventory} (S : Schedule I) (h : S.visits = 0) :
    IsEmpty (Burst S) := by
  refine ⟨fun b => ?_⟩
  have := b.val.isLt
  omega

theorem history_card_zero {I : Inventory} (S : Schedule I) (h : S.visits = 0) :
    Fintype.card (Recorder.Inputs S) = 1 := by
  simp only [Recorder.Inputs,Fintype.card_pi,Fintype.card_fin]
  haveI : IsEmpty (Fin S.visits) := by rw [h]; infer_instance
  simp

end History
end ScheduleLaw
