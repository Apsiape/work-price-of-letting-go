import GaugeCoordinates
import RegisterRefinement

/-! Coordinate splitting of the actual payload along any selected family
of distinct carriers. The complement retains all unselected carriers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def visitCarriers {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Finset (Fin I.count) := V.image S.carrier

def carrierVisits {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    {v // v ∈ V} ≃ {c // c ∈ visitCarriers S V} :=
  Equiv.ofBijective (fun v => ⟨S.carrier v.val,Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩)
    ⟨by
      intro v w he
      exact Subtype.ext (hc v.property w.property (congrArg Subtype.val he)),by
      intro c
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp c.property
      exact ⟨⟨v,hv⟩,Subtype.ext he⟩⟩

def visitPayloadPartition {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    Payload I ≃ Registers S V × Restricted I (visitCarriers S V)ᶜ :=
  (payloadPartition I (visitCarriers S V)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft (fun c : {c // c ∈ visitCarriers S V} => Fin (I.dim c.val))
        (carrierVisits S V hc)).symm (Equiv.refl _))

theorem visitPayloadPartition_selected {I : Inventory} (S : Schedule I)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (p : Payload I) (v : {v // v ∈ V}) :
    (visitPayloadPartition S V hc p).1 v = p (S.carrier v.val) := rfl

theorem visitPayloadPartition_rest {I : Inventory} (S : Schedule I)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (p : Payload I) (c : {c // c ∈ (visitCarriers S V)ᶜ}) :
    (visitPayloadPartition S V hc p).2 c = p c.val := rfl

/-- In the held frame, the payload's selected slots contain the actual
stored inputs. Moving them back gives all actual input records as one factor. -/
def heldRestCoordinates {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    (Record S Vᶜ Vᶜ × (Payload I × Fin r)) ≃
      (Recorder.Inputs S × Registers S Vᶜ) × (Restricted I (visitCarriers S V)ᶜ × Fin r) where
  toFun x := (((registerPartition S V).symm ((visitPayloadPartition S V hc x.2.1).1,x.1.1),x.1.2),
    ((visitPayloadPartition S V hc x.2.1).2,x.2.2))
  invFun x := (((registerPartition S V x.1.1).2,x.1.2),
    ((visitPayloadPartition S V hc).symm ((registerPartition S V x.1.1).1,x.2.1),x.2.2))
  left_inv x := by
    have hp := (registerPartition S V).apply_symm_apply ((visitPayloadPartition S V hc x.2.1).1,x.1.1)
    dsimp only
    rw [hp]
    simp only [Equiv.symm_apply_apply,Prod.mk.eta]
  right_inv x := by
    have hp := (visitPayloadPartition S V hc).apply_symm_apply ((registerPartition S V x.1.1).1,x.2.1)
    dsimp only
    rw [hp]
    simp only [Equiv.symm_apply_apply,Prod.mk.eta]

theorem heldRestCoordinates_actual {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (x : Raw S r) :
    (heldRestCoordinates S r V hc ((heldCoordinates S r V hc x).2)).1 =
      (x.1.1,fun v : {v // v ∈ Vᶜ} => x.1.2 v.val) := by
  apply Prod.ext
  · apply (registerPartition S V).injective
    change (registerPartition S V) ((registerPartition S V).symm _) = _
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · funext v
      change (gauge S r V hc x).2.1 (S.carrier v.val) = x.1.1 v.val
      exact gauge_payload_mem S r V hc v.val v.property x
    · funext v
      change (gauge S r V hc x).1.1 v.val = x.1.1 v.val
      exact gauge_preserves_input S r V hc v.val (Finset.mem_compl.mp v.property) x
  · change (fun v : {v // v ∈ Vᶜ} => (gauge S r V hc x).1.2 v.val) = _
    rw [gauge_preserves_partners]

theorem heldRestCoordinates_environment {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (x : Raw S r) :
    (heldRestCoordinates S r V hc ((heldCoordinates S r V hc x).2)).2 =
      (restrictPayload I (visitCarriers S V)ᶜ x.2.1,x.2.2) := by
  apply Prod.ext
  · funext c
    change (gauge S r V hc x).2.1 c.val = x.2.1 c.val
    apply gauge_preserves_carrier S r V hc c.val _ x
    intro w hw he
    exact (Finset.mem_compl.mp c.property) (Finset.mem_image.mpr ⟨w,hw,he.symm⟩)
  · exact gauge_preserves_memory S r V hc x

end History
end ScheduleLaw
