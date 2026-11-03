import PrefixCausality

/-! The last input burst is a lawful accessible record time. No subsequent
tester operation can change the retained record marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def arrivalEvents {I : Inventory} (S : Schedule I) : Finset (Event S) :=
  Finset.univ.image (fun v => S.position (v,false))

theorem arrivalEvents_nonempty {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    (arrivalEvents S).Nonempty :=
  ⟨S.position (⟨0,h⟩,false),Finset.mem_image.mpr ⟨⟨0,h⟩,Finset.mem_univ _,rfl⟩⟩

def lastArrival {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : Event S :=
  (arrivalEvents S).max' (arrivalEvents_nonempty S h)

theorem lastArrival_mem {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    lastArrival S h ∈ arrivalEvents S := Finset.max'_mem _ _

def lastArrivalVisit {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : Fin S.visits :=
  Classical.choose (Finset.mem_image.mp (lastArrival_mem S h))

theorem lastArrivalVisit_eq {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    S.position (lastArrivalVisit S h,false) = lastArrival S h :=
  (Classical.choose_spec (Finset.mem_image.mp (lastArrival_mem S h))).2

def lastInputBurst {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : InputBurst S :=
  inputBurst (lastArrivalVisit S h)

theorem all_inputs_before_last {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (v : Fin S.visits) : S.position (v,false) ≤ last (lastInputBurst S h).val := by
  have hmax : S.position (v,false) ≤ lastArrival S h :=
    Finset.le_max' (arrivalEvents S) _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  have hb : S.position (lastArrivalVisit S h,false) ∈ events (lastInputBurst S h).val :=
    burstOf_mem _
  have hl := ((mem_events_iff _ _).mp hb).2
  rw [lastArrivalVisit_eq] at hl
  exact hmax.trans hl

theorem last_inputs_complete {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    arrived S (recordTime (lastInputBurst S h)) = Finset.univ := by
  ext v
  simp only [Finset.mem_univ,iff_true,arrived_at_record]
  exact all_inputs_before_last S h v

theorem remaining_events_release {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (e : Event S) (he : last (lastInputBurst S h).val < e) : kind S e.val = true := by
  rcases hp : S.position.symm e with ⟨v,o⟩
  have hpos : S.position (v,o) = e := by
    simpa only [Equiv.apply_symm_apply] using (congrArg S.position hp).symm
  cases o with
  | true => rw [← hpos,kind_endpoint]
  | false =>
    have hv := all_inputs_before_last S h v
    rw [hpos] at hv
    exact False.elim (not_lt_of_ge hv he)

def firstFinalOutput {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : Event S :=
  ⟨(last (lastInputBurst S h).val).val+1,input_last_not_terminal (lastInputBurst S h)⟩

def finalOutputBurst {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : OutputBurst S :=
  ⟨burstOf (firstFinalOutput S h),by
    change kind S (start S (firstFinalOutput S h).val) = true
    rw [start_kind]
    exact remaining_events_release S h _ (by change _ < _+1; omega)⟩

theorem start_eq_on_interval {I : Inventory} (S : Schedule I) (p q : ℕ) (hpq : p ≤ q)
    (hk : ∀ n, p ≤ n → n ≤ q → kind S n = kind S p) : start S q = start S p := by
  induction q,hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    have he : kind S (q+1) = kind S q := (hk _ (by omega) le_rfl).trans (hk _ hpq (by omega)).symm
    rw [start,if_pos he]
    exact ih (fun n hn hq => hk n hn (by omega))

theorem final_output_burst_covers {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (e : Event S) (he : last (lastInputBurst S h).val < e) :
    burstOf e = (finalOutputBurst S h).val := by
  have hpq : (firstFinalOutput S h).val ≤ e.val := by
    change (last (lastInputBurst S h).val).val+1 ≤ e.val
    exact he
  have hk : ∀ n, (firstFinalOutput S h).val ≤ n → n ≤ e.val →
      kind S n = kind S (firstFinalOutput S h).val := by
    intro n hn hne
    have hnN : n < 2*S.visits := lt_of_le_of_lt hne e.isLt
    rw [remaining_events_release S h ⟨n,hnN⟩ (by
      change (last (lastInputBurst S h).val).val < n
      change (last (lastInputBurst S h).val).val+1 ≤ n at hn
      omega),remaining_events_release S h _ (by change _ < _+1; omega)]
  have hs := start_eq_on_interval S _ _ hpq hk
  apply Subtype.ext
  exact Fin.ext hs

theorem finalOutputBurst_start {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    (finalOutputBurst S h).val.val = firstFinalOutput S h := by
  apply Fin.ext
  change start S ((last (lastInputBurst S h).val).val+1) =
    (last (lastInputBurst S h).val).val+1
  rw [start]
  apply if_neg
  have hleft := same_kind (lastInputBurst S h).val _ (last_mem _)
  rw [(lastInputBurst S h).property] at hleft
  have hright := remaining_events_release S h (firstFinalOutput S h) (by change _ < _+1; omega)
  change kind S ((last (lastInputBurst S h).val).val+1) = true at hright
  rw [hleft,hright]
  decide

/-- Exactly the partners of final-burst outputs are omitted from the record.
All earlier output partners occur in the open-output dimension product. -/
theorem final_outputs_complement {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    outputVisits (finalOutputBurst S h) = (released S (recordTime (lastInputBurst S h)))ᶜ := by
  ext v
  simp only [outputVisits,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
  constructor
  · intro hm hr
    have hl := ((mem_events_iff _ _).mp hm).1
    rw [finalOutputBurst_start] at hl
    have hv : (S.position (v,true)).val+1 < (last (lastInputBurst S h).val).val+2 :=
      (Finset.mem_filter.mp hr).2
    change (last (lastInputBurst S h).val).val+1 ≤ (S.position (v,true)).val at hl
    omega
  · intro hn
    have he : last (lastInputBurst S h).val < S.position (v,true) := by
      simp only [released,recordTime,Finset.mem_filter,Finset.mem_univ,true_and] at hn
      change (last (lastInputBurst S h).val).val < (S.position (v,true)).val
      omega
    exact (burstOf_unique _ _).mpr (final_output_burst_covers S h _ he)

theorem tester_preserves_body {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (ρ : Mat (Global e r)) :
    partialRight (evolve (liftTesterObservable e r (t.gate k)) ρ) = partialRight ρ := by
  exact partialRight_evolve_one_kron _ ρ
    (unitary_submatrix (Equiv.prodComm (Payload I) (Fin r)) (t.unitary k))

theorem body_no_arrival {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) (hno : ∀ v, (Recorder.arrivalCut (S := S) v).val ≠ n) :
    partialRight (run (Recorder.extension S) t (n+1)) =
      partialRight (run (Recorder.extension S) t n) := by
  rw [run]
  split_ifs with hn
  · have hg : (Recorder.extension S).gate ⟨n,hn⟩ = 1 :=
      Recorder.gate_elsewhere _ (fun v he => hno v (congrArg Fin.val he))
    rw [jointGate_as_product,hg]
    have hl : liftDeviceObservable (Recorder.extension S) r 1 = 1 := by
      simp [liftDeviceObservable,one_kronecker_one,submatrix_one_equiv]
    rw [hl,mul_one]
    exact tester_preserves_body _ t _ _
  · rfl

theorem chi_as_body {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (n : ℕ)
    (A O : Finset (Fin S.visits)) :
    chi t n A O = partialRight
      (((partialRight (run (Recorder.extension S) t n)).submatrix (Recorder.stockFin S)
        (Recorder.stockFin S)).submatrix (stockPartition S A O).symm (stockPartition S A O).symm) := by
  ext i j
  change (∑ z : Record S Aᶜ Oᶜ × (Payload I × Fin r),
    run (Recorder.extension S) t n
      (Recorder.stockFin S ((stockPartition S A O).symm (i,z.1)),z.2)
      (Recorder.stockFin S ((stockPartition S A O).symm (j,z.1)),z.2)) =
    ∑ q : Record S Aᶜ Oᶜ, ∑ z : Payload I × Fin r,
      run (Recorder.extension S) t n
        (Recorder.stockFin S ((stockPartition S A O).symm (i,q)),z)
        (Recorder.stockFin S ((stockPartition S A O).symm (j,q)),z)
  exact Fintype.sum_prod_type _

theorem chi_no_arrival {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) (A O : Finset (Fin S.visits))
    (hno : ∀ v, (Recorder.arrivalCut (S := S) v).val ≠ n) : chi t (n+1) A O = chi t n A O := by
  rw [chi_as_body,chi_as_body,body_no_arrival S t n hno]

theorem body_after_last {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) (n : ℕ) (hn : recordTime (lastInputBurst S h) ≤ n) :
    partialRight (run (Recorder.extension S) t n) =
      partialRight (run (Recorder.extension S) t (recordTime (lastInputBurst S h))) := by
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [body_no_arrival S t n]
    · exact ih
    · intro v he
      have hv := all_inputs_before_last S h v
      change (S.position (v,false)).val ≤ (last (lastInputBurst S h).val).val at hv
      change (last (lastInputBurst S h).val).val+2 ≤ n at hn
      change (S.position (v,false)).val+1 = n at he
      omega

theorem terminal_record_accessible {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) :
    prefixChi (lastInputBurst S h) t = chi t (2*S.visits+1)
      (arrived S (recordTime (lastInputBurst S h))) (released S (recordTime (lastInputBurst S h))) := by
  unfold prefixChi
  rw [chi_as_body,chi_as_body,body_after_last S h t _ (recordTime_bound _)]

/-- The final accessible record equals the independently wired tester Gram
divided by the product of dimensions of outputs before the final burst. -/
theorem terminal_recorder_identity {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) :
    chi t (2*S.visits+1) (arrived S (recordTime (lastInputBurst S h)))
      (released S (recordTime (lastInputBurst S h))) =
      (prefixDimension (lastInputBurst S h) : ℂ)⁻¹ • prefixGram (lastInputBurst S h) t :=
  (terminal_record_accessible S h t).symm.trans (prefix_recorder_identity _ t)

end History
end ScheduleLaw
