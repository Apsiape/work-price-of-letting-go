import SwapGauge

/-! A family of visits simultaneously held at a fixed cut has distinct
physical carriers; all earlier SWAP-frame updates are exact finite set facts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def activeVisits {I : Inventory} (S : Schedule I) (k : Cut S) : Finset (Fin S.visits) :=
  Finset.univ.filter fun v => (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val

theorem activeVisits_carriers_injective {I : Inventory} (S : Schedule I) (k : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S k) :
    Set.InjOn S.carrier (V : Set (Fin S.visits)) := by
  intro v hv w hw hc
  exact active_visit_unique S k (Finset.mem_filter.mp (hV hv)).2
    (Finset.mem_filter.mp (hV hw)).2 hc

def considered {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) (n : ℕ) :
    Finset (Fin S.visits) := V ∩ arrived S n

theorem considered_subset {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) (n : ℕ) :
    considered S V n ⊆ V := Finset.inter_subset_left

theorem considered_zero {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    considered S V 0 = ∅ := by simp [considered,arrived]

theorem arrived_step_contact {I : Inventory} (S : Schedule I) (n : ℕ) (w : Fin S.visits)
    (hw : (Recorder.arrivalCut (S := S) w).val = n) :
    arrived S (n+1) = insert w (arrived S n) := by
  ext v
  simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · intro hv
    by_cases ho : (S.position (v,false)).val+1 < n
    · exact Or.inr ho
    · left
      apply Recorder.arrivalCut_injective (S := S)
      apply Fin.ext
      change (S.position (v,false)).val+1 = (S.position (w,false)).val+1
      change (S.position (w,false)).val+1 = n at hw
      omega
  · rintro (he | hv)
    · subst v
      change (S.position (w,false)).val+1 < n+1
      change (S.position (w,false)).val+1 = n at hw
      omega
    · omega

theorem arrived_step_none {I : Inventory} (S : Schedule I) (n : ℕ)
    (hno : ∀ v, (Recorder.arrivalCut (S := S) v).val ≠ n) : arrived S (n+1) = arrived S n := by
  ext v
  simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and]
  have hn := hno v
  change (S.position (v,false)).val+1 ≠ n at hn
  omega

theorem considered_step_inside {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (n : ℕ) (w : Fin S.visits) (hw : (Recorder.arrivalCut (S := S) w).val = n) (hmem : w ∈ V) :
    considered S V (n+1) = insert w (considered S V n) := by
  ext v
  simp only [considered,arrived_step_contact S n w hw,Finset.mem_inter,Finset.mem_insert]
  aesop

theorem considered_step_outside {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (n : ℕ) (w : Fin S.visits) (hw : (Recorder.arrivalCut (S := S) w).val = n) (hmem : w ∉ V) :
    considered S V (n+1) = considered S V n := by
  ext v
  simp only [considered,arrived_step_contact S n w hw,Finset.mem_inter,Finset.mem_insert]
  aesop

theorem considered_step_none {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (n : ℕ) (hno : ∀ v, (Recorder.arrivalCut (S := S) v).val ≠ n) :
    considered S V (n+1) = considered S V n := by rw [considered,considered,arrived_step_none S n hno]

theorem considered_not_new {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (n : ℕ) (w : Fin S.visits) (hw : (Recorder.arrivalCut (S := S) w).val = n) :
    w ∉ considered S V n := by
  intro hm
  have ha := (Finset.mem_filter.mp (Finset.mem_inter.mp hm).2).2
  change (S.position (w,false)).val+1 = n at hw
  omega

theorem considered_held {I : Inventory} (S : Schedule I) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) (n : ℕ) (hn : n ≤ K.val)
    (v : Fin S.visits) (hv : v ∈ considered S V (n+1)) :
    S.carrier v ∈ held S ⟨n,lt_of_le_of_lt hn K.isLt⟩ := by
  have hmem := (Finset.mem_inter.mp hv).1
  have ha := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  have hr := (Finset.mem_filter.mp (hV hmem)).2
  simp only [held,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨v,rfl,by omega,by omega⟩

theorem outside_contact_carrier_ne {I : Inventory} (S : Schedule I) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) (n : ℕ) (hn : n ≤ K.val)
    (w : Fin S.visits) (hw : (Recorder.arrivalCut (S := S) w).val = n) (hout : w ∉ V)
    (v : Fin S.visits) (hv : v ∈ considered S V n) : S.carrier w ≠ S.carrier v := by
  intro hc
  have hvV := (Finset.mem_inter.mp hv).1
  have ha := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  have hr := (Finset.mem_filter.mp (hV hvV)).2
  have hne : w ≠ v := fun he => hout (he ▸ hvV)
  have hwO := S.ordered w
  change (S.position (w,false)).val+1 = n at hw
  rcases S.disjoint w v hne hc with he | he <;> change _ < _ at he <;> omega

theorem considered_complete {I : Inventory} (S : Schedule I) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) : considered S V (K.val+1) = V := by
  ext v
  simp only [considered,Finset.mem_inter]
  constructor
  · exact And.left
  · intro hv
    have ha := (Finset.mem_filter.mp (hV hv)).2.1
    exact ⟨hv,by simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and]; omega⟩

def gaugeAt {I : Inventory} (S : Schedule I) (r : ℕ) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (n : ℕ) : Equiv.Perm (Raw S r) :=
  gauge S r (considered S V n) (hc.mono (considered_subset S V n))

theorem gauge_congr {I : Inventory} (S : Schedule I) (r : ℕ)
    (J J' : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (hc' : Set.InjOn S.carrier (J' : Set (Fin S.visits))) (he : J = J') :
    gauge S r J hc = gauge S r J' hc' := by subst J'; rfl

theorem gaugeAt_zero {I : Inventory} (S : Schedule I) (r : ℕ) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) : gaugeAt S r V hc 0 = 1 := by
  have he := gauge_congr S r (considered S V 0) ∅ (hc.mono (considered_subset S V 0))
    (hc.mono (by simp)) (considered_zero S V)
  exact he.trans (gauge_empty S r _)

theorem gaugeAt_contact_inside {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (n : ℕ) (w : Fin S.visits) (hw : (Recorder.arrivalCut (S := S) w).val = n) (hmem : w ∈ V) :
    gaugeAt S r V hc (n+1) = visitSwap S r w * gaugeAt S r V hc n := by
  have hsub : insert w (considered S V n) ⊆ V := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hmem
    · exact considered_subset S V n hv
  have he := gauge_congr S r _ _ (hc.mono (considered_subset S V (n+1))) (hc.mono hsub)
    (considered_step_inside S V n w hw hmem)
  exact he.trans (gauge_insert S r _ w (considered_not_new S V n w hw) (hc.mono hsub))

theorem gaugeAt_contact_outside {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (n : ℕ) (w : Fin S.visits) (hw : (Recorder.arrivalCut (S := S) w).val = n) (hmem : w ∉ V) :
    gaugeAt S r V hc (n+1) = gaugeAt S r V hc n :=
  gauge_congr S r _ _ _ _ (considered_step_outside S V n w hw hmem)

theorem gaugeAt_none {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (n : ℕ) (hno : ∀ v, (Recorder.arrivalCut (S := S) v).val ≠ n) :
    gaugeAt S r V hc (n+1) = gaugeAt S r V hc n :=
  gauge_congr S r _ _ _ _ (considered_step_none S V n hno)

theorem gaugeAt_complete {I : Inventory} (S : Schedule I) (r : ℕ) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    gaugeAt S r V (activeVisits_carriers_injective S K V hV) (K.val+1) =
      gauge S r V (activeVisits_carriers_injective S K V hV) :=
  gauge_congr S r _ _ _ _ (considered_complete S K V hV)

end History
end ScheduleLaw
