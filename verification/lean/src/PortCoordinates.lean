import ReleaseBend

/-! Actual visit-indexed port coordinates. A singled visit is separated
from every other held carrier, all other stocks and the complete reference.
Repeated loans retain their distinct stock indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

abbrev SinglePort {I : Inventory} (S : Schedule I) (v : Fin S.visits) := Registers S {v}
abbrev OtherStock {I : Inventory} (S : Schedule I) (v : Fin S.visits) := Record S {v}ᶜ {v}ᶜ
abbrev OutsidePorts {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) := Restricted I (visitCarriers S (insert v V))ᶜ

def insertedRegisters {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) : Registers S (insert v V) ≃ Registers S V × SinglePort S v where
  toFun a := (fun w => a ⟨w.val,Finset.mem_insert_of_mem w.property⟩,
    fun w => a ⟨w.val,Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp w.property))⟩)
  invFun a w := if hw : w.val ∈ V then a.1 ⟨w.val,hw⟩
    else a.2 ⟨w.val,Finset.mem_singleton.mpr ((Finset.mem_insert.mp w.property).resolve_right hw)⟩
  left_inv a := by
    funext w
    by_cases hw : w.val ∈ V <;> simp [hw]
  right_inv a := by
    apply Prod.ext
    · funext w; simp [w.property]
    · funext w
      have he : w.val = v := Finset.mem_singleton.mp w.property
      have hn : w.val ∉ V := by rw [he]; exact hv
      simp [hn]

def stockCoordinates {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    Recorder.Stock S ≃ PortStock (OtherStock S v) (SinglePort S v) :=
  (stockPartition S {v} {v}).trans (Equiv.prodComm _ _)

def payloadPortCoordinates {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    Payload I ≃ Registers S V × (SinglePort S v × OutsidePorts S V v) :=
  (visitPayloadPartition S (insert v V) hc).trans
    ((Equiv.prodCongr (insertedRegisters S V v hv) (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _))

theorem payloadPort_left {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (p : Payload I) (w : {w // w ∈ V}) :
    (payloadPortCoordinates S V v hv hc p).1 w = p (S.carrier w.val) := rfl

theorem payloadPort_single {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (p : Payload I) (w : {w // w ∈ ({v} : Finset (Fin S.visits))}) :
    (payloadPortCoordinates S V v hv hc p).2.1 w = p (S.carrier w.val) := rfl

theorem payloadPort_outside {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (p : Payload I) (w : {w // w ∈ (visitCarriers S (insert v V))ᶜ}) :
    (payloadPortCoordinates S V v hv hc p).2.2 w = p w.val := rfl

def portRaw {I : Inventory} (S : Schedule I) (r : ℕ) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    Raw S r ≃ PortInput (OtherStock S v) (Registers S V) (SinglePort S v)
      (OutsidePorts S V v × Fin r) where
  toFun x := ((stockCoordinates S v x.1,(payloadPortCoordinates S V v hv hc x.2.1).1),
    ((payloadPortCoordinates S V v hv hc x.2.1).2.1,
      ((payloadPortCoordinates S V v hv hc x.2.1).2.2,x.2.2)))
  invFun x := ((stockCoordinates S v).symm x.1.1,
    ((payloadPortCoordinates S V v hv hc).symm (x.1.2,(x.2.1,x.2.2.1)),x.2.2.2))
  left_inv x := by simp
  right_inv x := by simp

def physicalPort {I : Inventory} (S : Schedule I) (r : ℕ) (b : Type)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    b × (Payload I × Fin r) ≃ PortOutput b (Registers S V) (SinglePort S v)
      (OutsidePorts S V v × Fin r) where
  toFun x := ((x.1,(payloadPortCoordinates S V v hv hc x.2.1).1),
    ((payloadPortCoordinates S V v hv hc x.2.1).2.1,
      ((payloadPortCoordinates S V v hv hc x.2.1).2.2,x.2.2)))
  invFun x := (x.1.1,((payloadPortCoordinates S V v hv hc).symm
    (x.1.2,(x.2.1,x.2.2.1)),x.2.2.2))
  left_inv x := by simp
  right_inv x := by simp

theorem stockCoordinates_swap {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (x : Recorder.Stock S × Payload I) :
    stockCoordinates S v (Recorder.swapAt v x).1 =
      ((stockCoordinates S v x.1).1,((payloadPortCoordinates S V v hv hc x.2).2.1,
        (stockCoordinates S v x.1).2.2)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext w
      have hn : w.val ≠ v := by
        intro he
        exact (Finset.mem_compl.mp w.property) (Finset.mem_singleton.mpr he)
      exact Recorder.swapAt_other_input v w.val hn x
    · rfl
  · apply Prod.ext
    · funext w
      rcases w with ⟨w,hw⟩
      have he : w = v := Finset.mem_singleton.mp hw
      subst w
      exact Recorder.swapAt_input v x
    · rfl

theorem payloadPort_swap {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (v : Fin S.visits) (hv : v ∉ V) (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (x : Recorder.Stock S × Payload I) :
    payloadPortCoordinates S V v hv hc (Recorder.swapAt v x).2 =
      ((payloadPortCoordinates S V v hv hc x.2).1,
        ((stockCoordinates S v x.1).2.1,(payloadPortCoordinates S V v hv hc x.2).2.2)) := by
  apply Prod.ext
  · funext w
    rw [payloadPort_left,payloadPort_left]
    apply Recorder.swapAt_other_carrier
    intro he
    exact hv ((hc (Finset.mem_insert_of_mem w.property) (Finset.mem_insert_self v V) he) ▸ w.property)
  · apply Prod.ext
    · funext w
      rcases w with ⟨w,hw⟩
      have he : w = v := Finset.mem_singleton.mp hw
      subst w
      exact Recorder.swapAt_payload v x
    · funext w
      rw [payloadPort_outside,payloadPort_outside]
      apply Recorder.swapAt_other_carrier
      intro he
      exact (Finset.mem_compl.mp w.property)
        (Finset.mem_image.mpr ⟨v,Finset.mem_insert_self v V,he.symm⟩)

theorem portRaw_arrival {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) (x : Raw S r) :
    portRaw S r V v hv hc (wire (Recorder.arrivalCut (S := S) v) r x) =
      arrivalPermutation (OtherStock S v) (Registers S V) (SinglePort S v)
        (OutsidePorts S V v × Fin r) (portRaw S r V v hv hc x) := by
  rw [wire_apply,Recorder.contact_arrival]
  change ((stockCoordinates S v (Recorder.swapAt v (x.1,x.2.1)).1,
    (payloadPortCoordinates S V v hv hc (Recorder.swapAt v (x.1,x.2.1)).2).1),
    ((payloadPortCoordinates S V v hv hc (Recorder.swapAt v (x.1,x.2.1)).2).2.1,
      ((payloadPortCoordinates S V v hv hc (Recorder.swapAt v (x.1,x.2.1)).2).2.2,x.2.2))) = _
  rw [stockCoordinates_swap S V v hv hc,payloadPort_swap S V v hv hc]
  rfl

end ScheduleLaw.History.Wire
