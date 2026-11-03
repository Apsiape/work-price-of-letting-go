import PortCoordinates

/-! Arrival and release contraction on actual recorder histories. The
fresh-pair premise is derived from the actual circuit, including every
remaining stock, physical carrier and tester reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

theorem port_arrival_matrix {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    ((wire (Recorder.arrivalCut (S := S) v) r).permMatrix ℂ).submatrix
      (portRaw S r V v hv hc).symm (portRaw S r V v hv hc).symm =
        (arrivalPermutation (OtherStock S v) (Registers S V) (SinglePort S v)
          (OutsidePorts S V v × Fin r)).permMatrix ℂ := by
  apply Matrix.ext
  intro i j
  have he : wire (Recorder.arrivalCut (S := S) v) r ((portRaw S r V v hv hc).symm i) =
      (portRaw S r V v hv hc).symm j ↔
        arrivalPermutation (OtherStock S v) (Registers S V) (SinglePort S v)
          (OutsidePorts S V v × Fin r) i = j := by
    rw [← (portRaw S r V v hv hc).injective.eq_iff,portRaw_arrival,
      Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  simp only [submatrix_apply,Recorder.permutation_entry,he]
  split_ifs <;> rfl

def portRestCoordinates {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    OtherStock S v × (Payload I × Fin r) ≃
      PortRest (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r) where
  toFun x := (((x.1,(payloadPortCoordinates S V v hv hc x.2.1).2.1),
    (payloadPortCoordinates S V v hv hc x.2.1).1),
      ((payloadPortCoordinates S V v hv hc x.2.1).2.2,x.2.2))
  invFun x := (x.1.1.1,((payloadPortCoordinates S V v hv hc).symm
    (x.1.2,(x.1.1.2,x.2.1)),x.2.2))
  left_inv x := by simp
  right_inv x := by simp

theorem singleton_gauge {I : Inventory} (S : Schedule I) (r : ℕ) (v : Fin S.visits)
    (hc : Set.InjOn S.carrier (({v} : Finset (Fin S.visits)) : Set (Fin S.visits))) : gauge S r {v} hc = visitSwap S r v := by
  simp [gauge]

theorem portFresh_through_swap {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) (x : Raw S r) :
    freshCoordinates (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r)
      (portRaw S r V v hv hc (visitSwap S r v x)) =
        (Equiv.prodCongr (Equiv.prodComm (SinglePort S v) (SinglePort S v))
          (portRestCoordinates S r V v hv hc)) (recordCoordinates S r {v} {v} x) := by
  rw [show visitSwap S r v = wire (Recorder.arrivalCut (S := S) v) r from rfl,portRaw_arrival]
  rfl

theorem portFresh_coordinates {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (hs : Set.InjOn S.carrier (({v} : Finset (Fin S.visits)) : Set (Fin S.visits))) (x : Raw S r) :
    freshCoordinates (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r)
      (portRaw S r V v hv hc x) =
        (Equiv.prodCongr (Equiv.prodComm (SinglePort S v) (SinglePort S v))
          (portRestCoordinates S r V v hv hc)) (heldCoordinates S r {v} hs x) := by
  have he := portFresh_through_swap S r V v hv hc (visitSwap S r v x)
  have hvv : visitSwap S r v (visitSwap S r v x) = x := by
    change (visitSwap S r v * visitSwap S r v) x = x
    rw [visitSwap_square]
    rfl
  rw [hvv] at he
  simpa only [heldCoordinates,Equiv.trans_apply,singleton_gauge] using he

theorem tensor_reindex {a b c d : Type} (A : Mat a) (B : Mat b) (e : c ≃ a) (f : d ≃ b) :
    (A ⊗ₖ B).submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f) =
      A.submatrix e e ⊗ₖ B.submatrix f f := rfl

theorem epr_swap {c : Type} [Fintype c] [DecidableEq c] :
    (pureMatrix (Recorder.epr (a := c))).submatrix (Equiv.prodComm c c) (Equiv.prodComm c c) =
      pureMatrix (Recorder.epr (a := c)) := by
  ext i j
  simp [pureMatrix,Recorder.epr,eq_comm]

theorem heldState_raw_coordinates {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (W : Finset (Fin S.visits)) (hW : W ⊆ activeVisits S K) :
    heldState S t K W hW = (rawState t (K.val+1)).submatrix
      (heldCoordinates S r W (activeVisits_carriers_injective S K W hW)).symm
      (heldCoordinates S r W (activeVisits_carriers_injective S K W hW)).symm := by
  rw [heldState_actual_coordinates]
  rfl

theorem recorder_fresh_port_factor {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits))) (ha : v ∈ activeVisits S K) :
    ∃ ρ : Mat (PortRest (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r)),
      ρ.PosSemidef ∧ ρ.trace = 1 ∧
      (rawState t (K.val+1)).submatrix (portRaw S r V v hv hc).symm (portRaw S r V v hv hc).symm =
        ((pureMatrix (Recorder.epr (a := SinglePort S v))) ⊗ₖ ρ).submatrix
          (freshCoordinates (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r))
          (freshCoordinates (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r)) := by
  have hW : ({v} : Finset (Fin S.visits)) ⊆ activeVisits S K := by simpa using ha
  let H := heldState S t K {v} hW
  let R := portRestCoordinates S r V v hv hc
  let F := Equiv.prodCongr (Equiv.prodComm (SinglePort S v) (SinglePort S v)) R
  let C := freshCoordinates (OtherStock S v) (Registers S V) (SinglePort S v) (OutsidePorts S V v × Fin r)
  let P := portRaw S r V v hv hc
  let E := heldCoordinates S r {v} (activeVisits_carriers_injective S K {v} hW)
  let ρ := (partialLeft H).submatrix R.symm R.symm
  have hd := held_rest_density S t K {v} hW
  refine ⟨ρ,hd.1.submatrix _,(submatrix_trace_equiv R.symm _).trans hd.2,?_⟩
  have hcoord : P.trans C = E.trans F := by
    apply Equiv.ext
    intro x
    exact portFresh_coordinates S r V v hv hc _ x
  have hnew : ((rawState t (K.val+1)).submatrix P.symm P.symm).submatrix C.symm C.symm =
      H.submatrix F.symm F.symm := by
    dsimp only [H]
    rw [heldState_raw_coordinates]
    ext i j
    have hi := congrArg (fun e => e.symm i) hcoord
    have hj := congrArg (fun e => e.symm j) hcoord
    change P.symm (C.symm i) = E.symm (F.symm i) at hi
    change P.symm (C.symm j) = E.symm (F.symm j) at hj
    change (rawState t (K.val+1)) (P.symm (C.symm i)) (P.symm (C.symm j)) =
      (rawState t (K.val+1)) (E.symm (F.symm i)) (E.symm (F.symm j))
    rw [hi,hj]
  have hfactor : H.submatrix F.symm F.symm = pureMatrix (Recorder.epr (a := SinglePort S v)) ⊗ₖ ρ := by
    dsimp only [H]
    rw [fresh_held_pair_factor]
    change ((pureMatrix (Recorder.epr (a := SinglePort S v))) ⊗ₖ partialLeft H).submatrix
      (Equiv.prodCongr (Equiv.prodComm _ _) R.symm) (Equiv.prodCongr (Equiv.prodComm _ _) R.symm) = _
    rw [tensor_reindex,epr_swap]
  have heq := hnew.trans hfactor
  ext i j
  have ht := congrFun₂ heq (C i) (C j)
  simpa only [submatrix_apply,Equiv.symm_apply_apply] using ht

end ScheduleLaw.History.Wire
