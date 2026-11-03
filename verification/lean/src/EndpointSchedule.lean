import ActualPortRouting

/-! Every endpoint updates the held visit set exactly once. The release
contraction is specialized to the actual before-release recorder state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

def endpointBefore {I : Inventory} (S : Schedule I) (v : Fin S.visits) (o : Bool) : Cut S :=
  ⟨(S.position (v,o)).val,by have := (S.position (v,o)).isLt; omega⟩

def endpointAfter {I : Inventory} (S : Schedule I) (v : Fin S.visits) (o : Bool) : Cut S :=
  ⟨(S.position (v,o)).val+1,by have := (S.position (v,o)).isLt; omega⟩

theorem other_endpoint_ne {I : Inventory} (S : Schedule I) (v w : Fin S.visits)
    (hne : w ≠ v) (a b : Bool) : (S.position (w,a)).val ≠ (S.position (v,b)).val := by
  intro he
  exact hne (congrArg Prod.fst (S.position.injective (Fin.ext he)))

theorem active_arrival_update {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    activeVisits S (endpointAfter S v false) = insert v (activeVisits S (endpointBefore S v false)) := by
  ext w
  simp only [activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    endpointAfter,endpointBefore]
  by_cases he : w = v
  · subst w
    have hv := S.ordered v
    change (S.position (v,false)).val < (S.position (v,true)).val at hv
    simp
    omega
  · have ha := other_endpoint_ne S v w he false false
    have hr := other_endpoint_ne S v w he true false
    simp only [he,false_or]
    omega

theorem active_release_update {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    activeVisits S (endpointAfter S v true) = (activeVisits S (endpointBefore S v true)).erase v := by
  ext w
  simp only [activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,
    endpointAfter,endpointBefore]
  by_cases he : w = v
  · subst w; simp
  · have ha := other_endpoint_ne S v w he false true
    have hr := other_endpoint_ne S v w he true true
    have hvw : v ≠ w := Ne.symm he
    omega

theorem visit_active_before_release {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    v ∈ activeVisits S (endpointBefore S v true) := by
  simp only [activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,endpointBefore,le_refl,and_true]
  exact S.ordered v

def releaseOthers {I : Inventory} (S : Schedule I) (v : Fin S.visits) : Finset (Fin S.visits) :=
  (activeVisits S (endpointBefore S v true)).erase v

theorem releaseOthers_not_mem {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    v ∉ releaseOthers S v := Finset.notMem_erase _ _

theorem releaseOthers_insert {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    insert v (releaseOthers S v) = activeVisits S (endpointBefore S v true) :=
  Finset.insert_erase (visit_active_before_release S v)

theorem releasePorts_injective {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    Set.InjOn S.carrier ((insert v (releaseOthers S v) : Finset (Fin S.visits)) : Set (Fin S.visits)) := by
  rw [releaseOthers_insert]
  exact activeVisits_carriers_injective S _ _ (Finset.Subset.refl _)

def releasePortRaw {I : Inventory} (S : Schedule I) (r : ℕ) (v : Fin S.visits) :=
  portRaw S r (releaseOthers S v) v (releaseOthers_not_mem S v) (releasePorts_injective S v)

theorem actual_release_cross {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (v : Fin S.visits) (b d : Type)
    (K : Matrix ((b × Registers S (releaseOthers S v)) × SinglePort S v)
      ((PortStock (OtherStock S v) (SinglePort S v) × Registers S (releaseOthers S v)) × SinglePort S v) ℂ)
    (L : Matrix ((d × Registers S (releaseOthers S v)) × SinglePort S v)
      ((PortStock (OtherStock S v) (SinglePort S v) × Registers S (releaseOthers S v)) × SinglePort S v) ℂ) :
    heldLift (b := b) (s := OtherStock S v) (h := Registers S (releaseOthers S v)) (c := SinglePort S v) (u := OutsidePorts S (releaseOthers S v) v × Fin r) K *
      ((rawState t (endpointAfter S v true).val).submatrix (releasePortRaw S r v).symm (releasePortRaw S r v).symm) *
        (heldLift (b := d) (s := OtherStock S v) (h := Registers S (releaseOthers S v)) (c := SinglePort S v) (u := OutsidePorts S (releaseOthers S v) v × Fin r) L)ᴴ =
    unheldLift (b := b) (s := OtherStock S v) (h := Registers S (releaseOthers S v)) (c := SinglePort S v) (u := OutsidePorts S (releaseOthers S v) v × Fin r) (releaseKernel (b := b) (s := OtherStock S v) (h := Registers S (releaseOthers S v)) (c := SinglePort S v) K) *
      ((rawState t (endpointAfter S v true).val).submatrix (releasePortRaw S r v).symm (releasePortRaw S r v).symm) *
        (unheldLift (b := d) (s := OtherStock S v) (h := Registers S (releaseOthers S v)) (c := SinglePort S v) (u := OutsidePorts S (releaseOthers S v) v × Fin r) (releaseKernel (b := d) (s := OtherStock S v) (h := Registers S (releaseOthers S v)) (c := SinglePort S v) L))ᴴ := by
  obtain ⟨ρ,hρ,ht,hfactor⟩ := recorder_fresh_port_factor S t (endpointBefore S v true)
    (releaseOthers S v) v (releaseOthers_not_mem S v) (releasePorts_injective S v)
    (visit_active_before_release S v)
  simp only [releasePortRaw, endpointAfter, endpointBefore] at hfactor ⊢
  rw [hfactor]
  exact release_cross_state K L ρ

end ScheduleLaw.History.Wire
