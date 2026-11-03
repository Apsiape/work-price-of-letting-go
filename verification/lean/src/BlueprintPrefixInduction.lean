import BlueprintBurstGateWindows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem later_boundary_execution {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z)
    (t : Tester S (burstMemoryDim S)) (b : InputBurst S) (hb : 0<(inputRank b).val)
    (U : Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ))
    (hg : t.gate (burstPreparationCut b)=localRegisterGate I _ _ U)
    (hid : ∀ k : Cut S, (∀ a : InputBurst S, 0<(inputRank a).val → burstPreparationCut a≠k) → t.gate k=1)
    (hamp : ∀ x o w, (∑ m, previousPrefixAmplitude Z hZ b hb x m *
      (U*burstIncomingMatrix b hb) w (m,o))=
        ∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (x,o) a * burstOutgoingMatrix b hb w a)
    (hprev : amplitudes t (allBellSource S) (recordTime (previousInput b hb))=
      canonicalPrefixVector Z hZ (previousInput b hb)) :
    amplitudes t (allBellSource S) (recordTime b)=canonicalPrefixVector Z hZ b := by
  have hp : amplitudes t (allBellSource S) (burstPreparationCut b).val=
      canonicalPrefixVector Z hZ (previousInput b hb) :=
    (release_gap_execution t (allBellSource S) hid b hb).trans hprev
  have hw : wire (burstPreparationCut b) (burstMemoryDim S)=1 :=
    wire_identity_of_no_arrival _ _ (release_gap_no_arrival b hb _
      (earlier_recordTime_le_preparation _ _ (previous_lt b hb)) le_rfl)
  funext x
  rw [input_burst_execution t (allBellSource S) b (scheduled_input_gates t hid b) x]
  rw [amplitudes,dif_pos (burstPreparationCut b).isLt,hp]
  let y := gauge S (burstMemoryDim S) (inputVisits b) (inputVisits_carriers_injective b) x
  have hs := step_local_section t b U hg hw (canonicalPrefixVector Z hZ (previousInput b hb))
    (rawBurstCoordinates b y).1 (rawBurstCoordinates b y).2
  rw [Equiv.symm_apply_apply] at hs
  change step t (burstPreparationCut b) (canonicalPrefixVector Z hZ (previousInput b hb)) y=_
  rw [hs,burst_section_transport Z hZ b hb U hamp,Equiv.symm_apply_apply]
  exact congrArg (canonicalPrefixVector Z hZ b)
    (gauge_involutive S _ (inputVisits b) (inputVisits_carriers_injective b) x)

/-- The Recorder amplitude invariant is established by rank induction for
the actual fixed-memory tester assembled from the square local burst gates. -/
theorem canonical_recorder_prefixes {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0<S.visits) :
    ∃ t : Tester S (burstMemoryDim S), ∀ b,
      amplitudes t (allBellSource S) (recordTime b)=canonicalPrefixVector Z hZ b := by
  obtain ⟨t,U,ht,hU,hg,hid,hamp⟩ := canonical_burst_tester_gates Z hZ
    (firstPrefixInitialVector Z hZ h) (firstPrefixInitialVector_normalized Z hZ h)
  refine ⟨t,?_⟩
  have hi : ∀ n : ℕ, ∀ b : InputBurst S, (inputRank b).val=n →
      amplitudes t (allBellSource S) (recordTime b)=canonicalPrefixVector Z hZ b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hb
      by_cases hz : n=0
      · have he := rank_zero_first h b (hb.trans hz)
        subst b
        exact first_boundary_execution Z hZ h t ht (scheduled_first_gates h t hid)
      · have hp : 0<(inputRank b).val := by omega
        have hr := previous_rank b hp
        exact later_boundary_execution Z hZ t b hp (U b hp) (hg b hp) hid (hamp b hp)
          (ih (inputRank (previousInput b hp)).val (by omega) (previousInput b hp) rfl)
  exact fun b => hi _ b rfl

theorem positive_visit_comb_realization {I : Inventory} (S : Schedule I) (h : 0<S.visits)
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) :
    ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t=Z b := by
  obtain ⟨t,ht⟩ := canonical_recorder_prefixes Z hZ h
  exact ⟨burstMemoryDim S,t,fun b => prefixGram_of_canonical_vector Z hZ t b (ht b)⟩

end ScheduleLaw.Blueprint
