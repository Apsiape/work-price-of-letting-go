import RecorderGram

/-! Boundary cases of the causal prefix equations for actual tester gates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem first_event_arrival {I : Inventory} (S : Schedule I) (e : Event S) (he : e.val = 0) :
    kind S e.val = false := by
  rcases hp : S.position.symm e with ⟨v,o⟩
  have hpos : S.position (v,o) = e := by
    simpa only [Equiv.apply_symm_apply] using (congrArg S.position hp).symm
  cases o with
  | false => rw [← hpos,kind_endpoint]
  | true =>
    have hv := S.ordered v
    rw [hpos] at hv
    change (S.position (v,false)).val < e.val at hv
    omega

theorem last_event_release {I : Inventory} (S : Schedule I) (e : Event S)
    (he : e.val+1 = 2*S.visits) : kind S e.val = true := by
  rcases hp : S.position.symm e with ⟨v,o⟩
  have hpos : S.position (v,o) = e := by
    simpa only [Equiv.apply_symm_apply] using (congrArg S.position hp).symm
  cases o with
  | true => rw [← hpos,kind_endpoint]
  | false =>
    have hv := S.ordered v
    rw [hpos] at hv
    have hb := (S.position (v,true)).isLt
    change e.val < (S.position (v,true)).val at hv
    omega

def firstInputBurst {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : InputBurst S :=
  ⟨burstOf ⟨0,by omega⟩,by
    change kind S (start S 0) = false
    rw [start]
    exact first_event_arrival S ⟨0,by omega⟩ rfl⟩

theorem firstInputBurst_start {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    (firstInputBurst S h).val.val.val = 0 := rfl

theorem first_released_empty {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    released S (recordTime (firstInputBurst S h)) = ∅ := by
  ext v
  rw [released_at_record]
  change ((S.position (v,true)).val < 0) ↔ v ∈ (∅ : Finset (Fin S.visits))
  simp

theorem first_inputs {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    arrived S (recordTime (firstInputBurst S h)) = inputVisits (firstInputBurst S h) := by
  ext v
  rw [arrived_at_record]
  simp only [inputVisits,Finset.mem_filter,Finset.mem_univ,true_and,mem_events_iff]
  constructor
  · intro hv
    exact ⟨by change 0 ≤ _; omega,hv⟩
  · exact And.right

theorem first_dimension_one {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    prefixDimension (firstInputBurst S h) = 1 := by
  rw [prefixDimension,first_released_empty]
  simp [outputDimension]

/-- The first causal equation, with the first input burst traced, is an exact
consequence of the actual normalized coherent tester circuit. -/
theorem first_prefix_equation {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) :
    partialLeft (prefixGram (firstInputBurst S h) t) = 1 := by
  let b := firstInputBurst S h
  have hempty : released S (recordTime b) = ∅ := first_released_empty S h
  haveI : IsEmpty {v // v ∈ released S (recordTime b)} := by
    refine ⟨fun v => ?_⟩
    have hv := v.property
    simpa [hempty] using hv
  haveI : Nonempty (OutputPrefix b) :=
    ⟨fun v => ⟨0,I.dim_pos (S.carrier v.val)⟩⟩
  let ρ : Density (OutputPrefix b) :=
    ⟨partialLeft (prefixGram b t),partialLeft_positive (gram_positive t _ _ _),by
      rw [partialLeft_trace]
      exact (gram_trace t _ _ _).trans (by
        change (prefixDimension (firstInputBurst S h) : ℂ) = 1
        rw [first_dimension_one,Nat.cast_one])⟩
  exact density_subsingleton ρ

theorem prefix_gram_positive {I : Inventory} {S : Schedule I} {r : ℕ}
    (b : InputBurst S) (t : Tester S r) : (prefixGram b t).PosSemidef :=
  gram_positive t _ _ _

theorem prefix_gram_trace {I : Inventory} {S : Schedule I} {r : ℕ}
    (b : InputBurst S) (t : Tester S r) : (prefixGram b t).trace = prefixDimension b :=
  gram_trace t _ _ _

theorem zero_burst_card {I : Inventory} (S : Schedule I) (hz : S.visits = 0) :
    Fintype.card (Burst S) = 0 := by
  haveI := bursts_empty_of_zero S hz
  exact Fintype.card_of_isEmpty

end History
end ScheduleLaw
