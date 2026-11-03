import BlueprintKernelLocal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

theorem singled_carrier_not_mem {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    S.carrier v ∉ visitCarriers S V := by
  rintro h
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
  have hew := hc (Finset.mem_insert_of_mem hw) (Finset.mem_insert_self v V) he
  exact hv (hew ▸ hw)

theorem outside_insert_eq {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (p q : Payload I) :
    restrictPayload I (visitCarriers S V)ᶜ p=restrictPayload I (visitCarriers S V)ᶜ q ↔
      selectedVisits S {v} p=selectedVisits S {v} q ∧
      restrictPayload I (visitCarriers S (insert v V))ᶜ p=
        restrictPayload I (visitCarriers S (insert v V))ᶜ q := by
  rw [selectedVisits_eq_iff,restriction_eq_iff,restriction_eq_iff,restriction_eq_iff]
  have hn := singled_carrier_not_mem S V v hv hc
  simp only [visitCarriers,Finset.image_singleton,Finset.image_insert,Finset.mem_compl,
    Finset.mem_singleton,Finset.mem_insert,not_or] at hn ⊢
  constructor
  · intro h
    exact ⟨fun c he => he ▸ h (S.carrier v) hn,fun c hc' => h c hc'.2⟩
  · rintro ⟨hs,ho⟩ c hc'
    by_cases he : c=S.carrier v
    · exact hs c he
    · exact ho c ⟨he,hc'⟩

def unheldPortKernel {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits)
    (K : Matrix (b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    Matrix (b × Registers S V) (PortStock (OtherStock S v) (SinglePort S v) × Registers S V) ℂ :=
  K.submatrix id (Equiv.prodCongr (stockCoordinates S v).symm (Equiv.refl _))

def unheldFromPort {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits)
    (K : Matrix (b × Registers S V) (PortStock (OtherStock S v) (SinglePort S v) × Registers S V) ℂ) :
    Matrix (b × Registers S V) (Recorder.Stock S × Registers S V) ℂ :=
  K.submatrix id (Equiv.prodCongr (stockCoordinates S v) (Equiv.refl _))

def portHeldBody {I : Inventory} (S : Schedule I) (b : Type)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V) :
    b × Registers S (insert v V) ≃ (b × Registers S V) × SinglePort S v :=
  (Equiv.prodCongr (Equiv.refl b) (insertedRegisters S V v hv)).trans
    (Equiv.prodAssoc _ _ _).symm

def portHeldStock {I : Inventory} (S : Schedule I)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V) :
    Recorder.Stock S × Registers S (insert v V) ≃
      (PortStock (OtherStock S v) (SinglePort S v) × Registers S V) × SinglePort S v :=
  (Equiv.prodCongr (stockCoordinates S v) (insertedRegisters S V v hv)).trans
    (Equiv.prodAssoc _ _ _).symm

def heldPortKernel {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (K : Matrix (b × Registers S (insert v V)) (Recorder.Stock S × Registers S (insert v V)) ℂ) :
    Matrix ((b × Registers S V) × SinglePort S v)
      ((PortStock (OtherStock S v) (SinglePort S v) × Registers S V) × SinglePort S v) ℂ :=
  K.submatrix (portHeldBody S b V v hv).symm (portHeldStock S V v hv).symm

def heldFromPort {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (K : Matrix ((b × Registers S V) × SinglePort S v)
      ((PortStock (OtherStock S v) (SinglePort S v) × Registers S V) × SinglePort S v) ℂ) :
    Matrix (b × Registers S (insert v V)) (Recorder.Stock S × Registers S (insert v V)) ℂ :=
  K.submatrix (portHeldBody S b V v hv) (portHeldStock S V v hv)

theorem unheld_roundtrip {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits)
    (K : Matrix (b × Registers S V) (PortStock (OtherStock S v) (SinglePort S v) × Registers S V) ℂ) :
    unheldPortKernel V v (unheldFromPort V v K)=K := by
  ext i j
  simp [unheldPortKernel,unheldFromPort,Prod.map]

theorem held_roundtrip {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (K : Matrix ((b × Registers S V) × SinglePort S v)
      ((PortStock (OtherStock S v) (SinglePort S v) × Registers S V) × SinglePort S v) ℂ) :
    heldPortKernel V v hv (heldFromPort V v hv K)=K := by
  ext i j
  simp [heldPortKernel,heldFromPort]

theorem port_selected {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (p : Payload I) :
    (payloadPortCoordinates S V v hv hc p).1=selectedVisits S V p ∧
      (payloadPortCoordinates S V v hv hc p).2.1=selectedVisits S {v} p ∧
      (payloadPortCoordinates S V v hv hc p).2.2=
        restrictPayload I (visitCarriers S (insert v V))ᶜ p := by
  exact ⟨rfl,rfl,rfl⟩

theorem unheld_routed_port {I : Inventory} {S : Schedule I} {b : Type} (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (K : Matrix (b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    (routedLift r V (hc.mono (Finset.subset_insert v V)) K).submatrix
      (physicalPort S r b V v hv hc).symm (portRaw S r V v hv hc).symm =
        unheldLift (u := OutsidePorts S V v × Fin r) (unheldPortKernel V v K) := by
  have he (i : b × (Payload I × Fin r)) (j : Raw S r) :
      routedLift r V (hc.mono (Finset.subset_insert v V)) K i j =
        unheldLift (u := OutsidePorts S V v × Fin r) (unheldPortKernel V v K)
          (physicalPort S r b V v hv hc i) (portRaw S r V v hv hc j) := by
    simp only [routedLift_entry,outside_insert_eq S V v hv hc]
    simp only [unheldLift,unheldPortKernel,submatrix_apply,kroneckerMap_apply,one_apply,
      physicalPort,portRaw,Equiv.coe_fn_mk,Equiv.prodCongr_apply,Prod.map,
      Equiv.refl_apply,Equiv.symm_apply_apply,(port_selected S V v hv hc _).1,
      (port_selected S V v hv hc _).2.1,(port_selected S V v hv hc _).2.2,
      Prod.mk.injEq,and_assoc]
    rfl
  ext i j
  simpa only [submatrix_apply,Equiv.apply_symm_apply] using
    he ((physicalPort S r b V v hv hc).symm i) ((portRaw S r V v hv hc).symm j)

theorem held_routed_port {I : Inventory} {S : Schedule I} {b : Type} (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (K : Matrix (b × Registers S (insert v V)) (Recorder.Stock S × Registers S (insert v V)) ℂ) :
    (routedLift r (insert v V) hc K).submatrix
      (physicalPort S r b V v hv hc).symm (portRaw S r V v hv hc).symm =
        heldLift (u := OutsidePorts S V v × Fin r) (heldPortKernel V v hv K) := by
  have he (i : b × (Payload I × Fin r)) (j : Raw S r) :
      routedLift r (insert v V) hc K i j =
        heldLift (u := OutsidePorts S V v × Fin r) (heldPortKernel V v hv K)
          (physicalPort S r b V v hv hc i) (portRaw S r V v hv hc j) := by
    rw [routedLift_entry]
    simp only [heldLift,heldPortKernel,submatrix_apply,kroneckerMap_apply,one_apply,
      physicalPort,portRaw,Equiv.coe_fn_mk,Equiv.prodAssoc_symm_apply,
      portHeldBody,portHeldStock,Equiv.symm_trans_apply,Equiv.trans_apply,
      Equiv.symm_symm,Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,
      Prod.map,payloadPortCoordinates,Equiv.prodAssoc_apply,
      Equiv.symm_apply_apply,Prod.mk.eta,routed_selected,routed_outside,Prod.mk.injEq]
    rfl
  ext i j
  simpa only [submatrix_apply,Equiv.apply_symm_apply] using
    he ((physicalPort S r b V v hv hc).symm i) ((portRaw S r V v hv hc).symm j)

#print axioms singled_carrier_not_mem
#print axioms outside_insert_eq
#print axioms unheldPortKernel
#print axioms unheldFromPort
#print axioms portHeldBody
#print axioms portHeldStock
#print axioms heldPortKernel
#print axioms heldFromPort
#print axioms unheld_roundtrip
#print axioms held_roundtrip
#print axioms port_selected
#print axioms unheld_routed_port
#print axioms held_routed_port
end ScheduleLaw.Blueprint
