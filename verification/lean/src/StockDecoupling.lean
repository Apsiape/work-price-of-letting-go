import FreshPartners
import VisitPayload

/-! Fresh retained partners factor from every stock input and every other
partner. This is a circuit marginal statement, before choosing a prefix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem partialRight_prod_equiv {a b c d : Type} [Fintype b] [Fintype d]
    (e : a ≃ c) (f : b ≃ d) (ρ : Mat (c × d)) :
    partialRight (ρ.submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f)) =
      (partialRight ρ).submatrix e e := by
  ext i j
  exact Equiv.sum_comp f (fun z => ρ (e i,z) (e j,z))

def crossCoordinates (a b c d : Type) : ((a × b) × (c × d)) ≃ ((b × c) × (a × d)) where
  toFun x := ((x.1.2,x.2.1),(x.1.1,x.2.2))
  invFun x := ((x.2.1,x.1.1),(x.1.2,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem cross_trace_factor {a b c d : Type} [Fintype a] [Fintype d]
    (A : Mat (a × b)) (B : Mat (c × d)) :
    partialRight ((A ⊗ₖ B).submatrix (crossCoordinates a b c d).symm
      (crossCoordinates a b c d).symm) = partialLeft A ⊗ₖ partialRight B := by
  ext i j
  simp only [partialRight,partialLeft,submatrix_apply,crossCoordinates,
    Equiv.coe_fn_symm_mk,kroneckerMap_apply,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

def stockOutputPartition {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Recorder.Stock S ≃ Registers S V × (Recorder.Inputs S × Registers S Vᶜ) where
  toFun x := ((registerPartition S V x.2).1,(x.1,(registerPartition S V x.2).2))
  invFun x := (x.2.1,(registerPartition S V).symm (x.1,x.2.2))
  left_inv x := by dsimp only; rw [Equiv.symm_apply_apply]
  right_inv x := by dsimp only; rw [Equiv.apply_symm_apply]

def payloadEnvironment {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    (Payload I × Fin r) ≃ Registers S V × (Restricted I (visitCarriers S V)ᶜ × Fin r) :=
  (Equiv.prodCongr (visitPayloadPartition S V hc) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

theorem held_complete_route {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    ((heldCoordinates S r V hc).trans
      (Equiv.prodCongr (Equiv.refl _) (heldRestCoordinates S r V hc))).trans
        (crossCoordinates _ _ _ _) =
      Equiv.prodCongr (stockOutputPartition S V) (payloadEnvironment S r V hc) := by
  apply Equiv.ext
  intro x
  change (((heldCoordinates S r V hc x).1.2,
      (heldRestCoordinates S r V hc ((heldCoordinates S r V hc x).2)).1),
    ((heldCoordinates S r V hc x).1.1,
      (heldRestCoordinates S r V hc ((heldCoordinates S r V hc x).2)).2)) = _
  rw [heldCoordinates_halves,heldRestCoordinates_actual,heldRestCoordinates_environment]
  rfl

theorem heldState_pullback {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    rawState t (K.val+1) = (heldState S t K V hV).submatrix
      (heldCoordinates S r V (activeVisits_carriers_injective S K V hV))
      (heldCoordinates S r V (activeVisits_carriers_injective S K V hV)) := by
  rw [heldState_actual_coordinates]
  ext i j
  simp only [submatrix_apply,Equiv.trans_apply,Equiv.symm_apply_apply,rawState]

def completeRestRecord {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    Mat (Recorder.Inputs S × Registers S Vᶜ) :=
  partialRight ((partialLeft (heldState S t K V hV)).submatrix
    (heldRestCoordinates S r V (activeVisits_carriers_injective S K V hV)).symm
    (heldRestCoordinates S r V (activeVisits_carriers_injective S K V hV)).symm)

/-- Flatness is joint with all stored inputs and all unselected partners,
not just with a chosen old-record marginal. -/
theorem fresh_complete_stock {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    (partialRight (rawState t (K.val+1))).submatrix
      (stockOutputPartition S V).symm (stockOutputPartition S V).symm =
      ((outputDimension S V : ℂ)⁻¹ • (1 : Mat (Registers S V))) ⊗ₖ
        completeRestRecord S t K V hV := by
  let hc := activeVisits_carriers_injective S K V hV
  let R := heldRestCoordinates S r V hc
  let P := payloadEnvironment S r V hc
  let C := crossCoordinates (Registers S V) (Registers S V)
    (Recorder.Inputs S × Registers S Vᶜ) (Restricted I (visitCarriers S V)ᶜ × Fin r)
  have he : (rawState t (K.val+1)).submatrix
      (Equiv.prodCongr (stockOutputPartition S V).symm P.symm)
      (Equiv.prodCongr (stockOutputPartition S V).symm P.symm) =
      ((pureMatrix (Recorder.epr (a := Registers S V))) ⊗ₖ
        ((partialLeft (heldState S t K V hV)).submatrix R.symm R.symm)).submatrix C.symm C.symm := by
    rw [heldState_pullback S t K V hV]
    have hr := held_complete_route S r V hc
    have hinv := congrArg Equiv.symm hr
    have hcoord : (Equiv.prodCongr (stockOutputPartition S V).symm P.symm).trans
        (heldCoordinates S r V hc) = C.symm.trans (Equiv.prodCongr (Equiv.refl _) R.symm) := by
      apply Equiv.ext
      intro x
      have h := congrArg (fun e => e x) hinv
      simpa only [Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
        using (congrArg (heldCoordinates S r V hc) h).symm
    ext i j
    change heldState S t K V hV
      (((Equiv.prodCongr (stockOutputPartition S V).symm P.symm).trans (heldCoordinates S r V hc)) i)
      (((Equiv.prodCongr (stockOutputPartition S V).symm P.symm).trans (heldCoordinates S r V hc)) j) = _
    rw [hcoord]
    nth_rw 1 [fresh_held_pair_factor]
    rfl
  rw [← partialRight_prod_equiv (stockOutputPartition S V).symm P.symm,he,
    cross_trace_factor,epr_left_reduction,registers_card]
  rfl

end History
end ScheduleLaw
