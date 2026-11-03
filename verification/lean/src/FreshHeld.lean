import HeldSchedule
import EPRTensor
import GaugeCoordinates

/-! A joint EPR invariant for every selected family of simultaneously held
visits. The moving SWAP frame keeps their halves in fixed stock coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def rawState {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (n : ℕ) : Mat (Raw S r) :=
  (run (Recorder.extension S) t n).submatrix (actual S r) (actual S r)

def gaugedState {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (n : ℕ) :
    Mat (Raw S r) := (rawState t n).submatrix (gaugeAt S r V hc n) (gaugeAt S r V hc n)

theorem perm_submatrix_mul {x : Type} (ρ : Mat x) (σ τ : Equiv.Perm x) :
    (ρ.submatrix σ σ).submatrix τ τ = ρ.submatrix (σ*τ) (σ*τ) := rfl

theorem raw_joint_matrix {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (k : Cut S) :
    (jointGate (Recorder.extension S) t k).submatrix (actual S r) (actual S r) =
      testerOperator t k * (wire k r).permMatrix ℂ := by
  rw [jointGate_as_product,← submatrix_mul_equiv _ _ (actual S r) (actual S r) (actual S r),
    device_raw,testerOperator_actual]

theorem rawState_step {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) (hn : n < 2*S.visits+1) :
    rawState t (n+1) = evolve (testerOperator t ⟨n,hn⟩ * (wire (⟨n,hn⟩ : Cut S) r).permMatrix ℂ)
      (rawState t n) := by
  unfold rawState
  rw [run,dif_pos hn,← evolve_submatrix_equiv (actual S r),raw_joint_matrix]

theorem gauged_step_marginal {I : Inventory} (S : Schedule I) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) {r : ℕ} (t : Tester S r)
    (n : ℕ) (hn : n ≤ K.val) :
    rawMarginal S r V V (gaugedState t V (activeVisits_carriers_injective S K V hV) (n+1)) =
      rawMarginal S r V V ((rawState t n).submatrix
        (wire (⟨n,lt_of_le_of_lt hn K.isLt⟩ : Cut S) r *
          gaugeAt S r V (activeVisits_carriers_injective S K V hV) (n+1) : Equiv.Perm (Raw S r))
        (wire (⟨n,lt_of_le_of_lt hn K.isLt⟩ : Cut S) r *
          gaugeAt S r V (activeVisits_carriers_injective S K V hV) (n+1) : Equiv.Perm (Raw S r))) := by
  let hc := activeVisits_carriers_injective S K V hV
  let k : Cut S := ⟨n,lt_of_le_of_lt hn K.isLt⟩
  have hT : (testerOperator t k).submatrix (gaugeAt S r V hc (n+1)) (gaugeAt S r V hc (n+1)) =
      testerOperator t k :=
    tester_gauge_invariant S t k _ _ (fun v hv => considered_held S K V hV n hn v hv)
  rw [gaugedState,rawState_step S t n k.isLt,evolve_mul,
    ← evolve_submatrix_equiv (gaugeAt S r V hc (n+1)),hT,
    testerOperator_preserves_record,Recorder.permutation_evolve,perm_submatrix_mul]

/-- Exact joint purity of the fixed-frame selected pairs throughout the
initialized history up to the cut at which they are all held. -/
theorem gauged_fresh_marginal {I : Inventory} (S : Schedule I) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) {r : ℕ} (t : Tester S r)
    (m : ℕ) (hm : m ≤ K.val+1) :
    rawMarginal S r V V (gaugedState t V (activeVisits_carriers_injective S K V hV) m) =
      pureMatrix (Recorder.epr (a := Registers S V)) := by
  let hc := activeVisits_carriers_injective S K V hV
  induction m with
  | zero =>
    rw [gaugedState,gaugeAt_zero]
    exact initial_pair_marginal S t V
  | succ n ih =>
    have hn : n ≤ K.val := by omega
    have hnN : n < 2*S.visits+1 := lt_of_le_of_lt hn K.isLt
    have hprev := ih (by omega)
    rw [gauged_step_marginal S K V hV t n hn]
    by_cases hw : ∃ w, Recorder.arrivalCut (S := S) w = (⟨n,hnN⟩ : Cut S)
    · obtain ⟨w,hw⟩ := hw
      have hwval : (Recorder.arrivalCut (S := S) w).val = n := congrArg Fin.val hw
      by_cases hwV : w ∈ V
      · have hg := gaugeAt_contact_inside S r V hc n w hwval hwV
        rw [← hw,hg]
        change rawMarginal S r V V ((rawState t n).submatrix
          (visitSwap S r w * (visitSwap S r w * gaugeAt S r V hc n) : Equiv.Perm (Raw S r))
          (visitSwap S r w * (visitSwap S r w * gaugeAt S r V hc n) : Equiv.Perm (Raw S r))) = _
        rw [← mul_assoc,visitSwap_square,one_mul]
        exact hprev
      · have hg := gaugeAt_contact_outside S r V hc n w hwval hwV
        have hcomm := gauge_commute_swap S r (considered S V n)
          (hc.mono (considered_subset S V n)) w
          (fun v hv => outside_contact_carrier_ne S K V hV n hn w hwval hwV v hv)
        rw [← hw,hg]
        change rawMarginal S r V V ((rawState t n).submatrix
          (visitSwap S r w * gaugeAt S r V hc n : Equiv.Perm (Raw S r)) (visitSwap S r w * gaugeAt S r V hc n : Equiv.Perm (Raw S r))) = _
        change Commute (visitSwap S r w) (gaugeAt S r V hc n) at hcomm
        rw [hcomm.eq,← perm_submatrix_mul]
        exact (rawMarginal_arrival S r w V V hwV _).trans hprev
    · have hno : ∀ v, (Recorder.arrivalCut (S := S) v).val ≠ n := by
        intro v hv
        exact hw ⟨v,Fin.ext hv⟩
      have hwire : wire (⟨n,hnN⟩ : Cut S) r = 1 := by
        apply Equiv.ext
        intro x
        rw [wire_apply]
        have he : Recorder.contact (⟨n,hnN⟩ : Cut S) = Equiv.refl _ := by
          simp only [Recorder.contact,dif_neg hw]
        rw [he]
        rfl
      rw [hwire,one_mul,gaugeAt_none S r V hc n hno]
      exact hprev

/-- A coordinate frame for the actual selected held halves and partners. The
remaining factor includes every other physical register and tester reference. -/
def heldState {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    Mat (Record S V V × (Record S Vᶜ Vᶜ × (Payload I × Fin r))) :=
  (gaugedState t V (activeVisits_carriers_injective S K V hV) (K.val+1)).submatrix
    (recordCoordinates S r V V).symm (recordCoordinates S r V V).symm

theorem heldState_actual_coordinates {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (K : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    heldState S t K V hV = (run (Recorder.extension S) t (K.val+1)).submatrix
      ((heldCoordinates S r V (activeVisits_carriers_injective S K V hV)).symm.trans (actual S r))
      ((heldCoordinates S r V (activeVisits_carriers_injective S K V hV)).symm.trans (actual S r)) := by
  unfold heldState gaugedState
  rw [gaugeAt_complete S r K V hV]
  ext i j
  change run (Recorder.extension S) t (K.val+1)
      (actual S r (gauge S r V _ ((recordCoordinates S r V V).symm i)))
      (actual S r (gauge S r V _ ((recordCoordinates S r V V).symm j))) =
    run (Recorder.extension S) t (K.val+1)
      (actual S r ((gauge S r V _).symm ((recordCoordinates S r V V).symm i)))
      (actual S r ((gauge S r V _).symm ((recordCoordinates S r V V).symm j)))
  rw [gauge_symm]

theorem heldState_trace {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) : (heldState S t K V hV).trace = 1 := by
  rw [heldState,submatrix_trace_equiv,gaugedState,submatrix_trace_equiv,rawState,submatrix_trace_equiv]
  exact (run_density (Recorder.extension S) t _).2

theorem heldState_marginal {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    partialRight (heldState S t K V hV) = pureMatrix (Recorder.epr (a := Registers S V)) :=
  gauged_fresh_marginal S K V hV t _ le_rfl

/-- The joint selected EPR state factors exactly from the complete physical
rest. No independence condition on that rest is a premise. -/
theorem fresh_held_pair_factor {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    heldState S t K V hV = pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
      partialLeft (heldState S t K V hV) := by
  let ψ := fun x => amplitudes t Recorder.epr (K.val+1)
    (gaugeAt S r V (activeVisits_carriers_injective S K V hV) (K.val+1)
      ((recordCoordinates S r V V).symm x))
  have hp : heldState S t K V hV = pureMatrix ψ := by
    rw [heldState,gaugedState,rawState,run_amplitudes]
    rfl
  have ht : (pureMatrix ψ).trace = 1 := hp ▸ heldState_trace S t K V hV
  rw [pureMatrix_trace] at ht
  have hn : ∑ x, Complex.normSq (ψ x) = 1 := congrArg Complex.re ht
  have hm : partialRight (pureMatrix ψ) = pureMatrix (Recorder.epr (a := Registers S V)) := by
    rw [← hp]
    exact heldState_marginal S t K V hV
  rw [hp]
  exact pure_marginal_factor ψ _ hn Recorder.epr_normalized hm

theorem held_rest_density {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    (partialLeft (heldState S t K V hV)).PosSemidef ∧
      (partialLeft (heldState S t K V hV)).trace = 1 := by
  constructor
  · apply partialLeft_positive
    unfold heldState gaugedState rawState
    exact (((run_density (Recorder.extension S) t _).1.submatrix _).submatrix _).submatrix _
  · rw [partialLeft_trace,heldState_trace]

end History
end ScheduleLaw
