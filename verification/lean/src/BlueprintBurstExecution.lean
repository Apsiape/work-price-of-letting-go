import BlueprintCanonicalBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem step_identity_gate {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S) (hg : t.gate k=1) (v : Raw S r → ℂ) (x : Raw S r) :
    step t k v x=v (wire k r x) := by
  simp [step,hg,Matrix.one_apply,Fintype.sum_prod_type,Prod.mk.injEq,ite_mul,ite_and]

theorem wire_identity_of_no_arrival {I : Inventory} {S : Schedule I} (r : ℕ)
    (k : Cut S) (hno : ∀ v, (Recorder.arrivalCut (S := S) v).val≠k.val) : wire k r=1 := by
  have hn : ¬∃ v, Recorder.arrivalCut (S := S) v=k := by
    rintro ⟨v,hv⟩
    exact hno v (congrArg Fin.val hv)
  apply Equiv.ext
  intro x
  rw [wire_apply]
  have hc : Recorder.contact k=Equiv.refl _ := by simp only [Recorder.contact,dif_neg hn]
  rw [hc]
  rfl

theorem gaugeAt_right_step {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (n : ℕ) (hn : n<2*S.visits+1)
    (harrival : ∀ v, (Recorder.arrivalCut (S := S) v).val=n → v∈V) :
    gaugeAt S r V hc (n+1)=gaugeAt S r V hc n*wire (⟨n,hn⟩:Cut S) r := by
  by_cases hw : ∃ v, Recorder.arrivalCut (S := S) v=(⟨n,hn⟩:Cut S)
  · obtain ⟨v,hv⟩ := hw
    have hvn := congrArg Fin.val hv
    have hvV := harrival v hvn
    have hcomm := gauge_commute_swap S r (considered S V n)
      (hc.mono (considered_subset S V n)) v (by
        intro w hw he
        have heq := hc hvV (considered_subset S V n hw) he
        subst w
        exact considered_not_new S V n v hvn hw)
    change Commute (visitSwap S r v) (gaugeAt S r V hc n) at hcomm
    rw [gaugeAt_contact_inside S r V hc n v hvn hvV,←hv]
    exact hcomm.eq
  · have hno : ∀ v, (Recorder.arrivalCut (S := S) v).val≠n := by
      intro v hv
      exact hw ⟨v,Fin.ext hv⟩
    rw [gaugeAt_none S r V hc n hno,wire_identity_of_no_arrival r _ hno,mul_one]

/-- In an identity-gate interval, only the selected Recorder SWAPs act.
The statement holds for any input amplitude, including unnormalized Bell stock. -/
theorem amplitudes_idle_gauge {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (φ : Recorder.Stock S → ℂ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (start finish : ℕ) (hsf : start≤finish) (hf : finish≤2*S.visits+1)
    (hstart : considered S V start=∅)
    (hg : ∀ k : Cut S, start≤k.val → k.val<finish → t.gate k=1)
    (ha : ∀ n, start≤n → n<finish → ∀ v, (Recorder.arrivalCut (S := S) v).val=n → v∈V) :
    ∀ x, amplitudes t φ finish x=amplitudes t φ start (gaugeAt S r V hc finish x) := by
  have hzero : gaugeAt S r V hc start=1 := by
    exact (gauge_congr S r _ _ _ (hc.mono (by simp)) hstart).trans (gauge_empty S r _)
  have h : ∀ d : ℕ, start+d≤finish → ∀ x,
      amplitudes t φ (start+d) x=amplitudes t φ start (gaugeAt S r V hc (start+d) x) := by
    intro d
    induction d with
    | zero => intro _ x; simp only [add_zero,hzero,Equiv.Perm.one_apply]
    | succ d ih =>
      intro hd x
      have hn : start+d<2*S.visits+1 := by omega
      have hl : start+d<finish := by omega
      have he := gaugeAt_right_step S r V hc (start+d) hn (ha _ (by omega) hl)
      have hi := ih (by omega) (wire (⟨start+d,hn⟩:Cut S) r x)
      rw [show start+(d+1)=(start+d)+1 by omega,amplitudes,dif_pos hn,
        step_identity_gate t ⟨start+d,hn⟩ (hg ⟨start+d,hn⟩ (by change start ≤ start+d; omega) hl),hi,he]
      rfl
  have hd : start+(finish-start)=finish := by omega
  intro x
  simpa only [hd] using h (finish-start) (by omega) x

theorem input_burst_considered_start {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    considered S (inputVisits b) ((burstPreparationCut b).val+1)=∅ := by
  ext v
  constructor
  · intro hv'
    obtain ⟨hv,ha⟩ := Finset.mem_inter.mp hv'
    have hi := ((mem_events_iff b.val _).mp (Finset.mem_filter.mp hv).2).1
    have hs : b.val.val.val≤(S.position (v,false)).val := hi
    simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and,burstPreparationCut] at ha
    omega
  · intro hv
    simp at hv

theorem input_burst_arrivals {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (n : ℕ) (hs : (burstPreparationCut b).val+1≤n) (hf : n<recordTime b)
    (v : Fin S.visits) (hv : (Recorder.arrivalCut (S := S) v).val=n) : v∈inputVisits b := by
  simp only [inputVisits,Finset.mem_filter,Finset.mem_univ,true_and]
  apply (mem_events_iff b.val _).mpr
  change (S.position (v,false)).val+1=n at hv
  simp only [burstPreparationCut,recordTime] at hs hf
  constructor
  · change b.val.val.val≤(S.position (v,false)).val
    omega
  · change (S.position (v,false)).val≤(last b.val).val
    omega

theorem input_burst_execution {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (φ : Recorder.Stock S → ℂ) (b : InputBurst S)
    (hg : ∀ k : Cut S, (burstPreparationCut b).val+1≤k.val → k.val<recordTime b → t.gate k=1) :
    ∀ x, amplitudes t φ (recordTime b) x=
      amplitudes t φ ((burstPreparationCut b).val+1)
        (gauge S r (inputVisits b) (inputVisits_carriers_injective b) x) := by
  have hs : b.val.val.val≤(last b.val).val := first_le_last b.val
  have h := amplitudes_idle_gauge t φ (inputVisits b) (inputVisits_carriers_injective b)
    ((burstPreparationCut b).val+1) (recordTime b)
    (by simp only [burstPreparationCut,recordTime]; omega)
    (recordTime_bound b) (input_burst_considered_start b) hg (input_burst_arrivals b)
  have he : gaugeAt S r (inputVisits b) (inputVisits_carriers_injective b) (recordTime b)=
      gauge S r (inputVisits b) (inputVisits_carriers_injective b) :=
    gauge_congr S r _ _ _ _ (considered_complete S (prefixCut b) _ (inputVisits_active_at_prefix b))
  simpa only [he] using h

theorem release_gap_no_arrival {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (n : ℕ)
    (hs : recordTime (previousInput b hb)≤n) (hf : n≤(burstPreparationCut b).val) :
    ∀ v, (Recorder.arrivalCut (S := S) v).val≠n := by
  intro v hv
  have hl := start_le S (S.position (v,false)).val
  have hbefore : inputBurst v<b := by
    change start S (S.position (v,false)).val<b.val.val.val
    change (S.position (v,false)).val+1=n at hv
    simp only [burstPreparationCut] at hf
    omega
  have hprev := le_previous b hb (inputBurst v) hbefore
  have hpos := ((mem_events_iff (inputBurst v).val _).mp (burstOf_mem _)).2
  have hlast := burst_last_mono (inputBurst v).val (previousInput b hb).val hprev
  have he : (S.position (v,false)).val≤(last (previousInput b hb).val).val := le_trans hpos hlast
  change (S.position (v,false)).val+1=n at hv
  simp only [recordTime] at hs
  omega

end ScheduleLaw.Blueprint
