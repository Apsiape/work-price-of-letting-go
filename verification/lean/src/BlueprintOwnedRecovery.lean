import BlueprintKernelInduction
import BlueprintStockPast

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

def ownedPairFrame {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Recorder.Stock S × Registers S V ≃ Record S V V × (Recorder.Inputs S × Registers S Vᶜ) where
  toFun x := ((x.2,(stockOutputPartition S V x.1).1),(stockOutputPartition S V x.1).2)
  invFun x := ((stockOutputPartition S V).symm (x.1.2,x.2),x.1.1)
  left_inv x := by simp
  right_inv x := by simp

theorem owned_fresh_route {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    ((routedFrame S (Recorder.Stock S) r V hc).trans
      (Equiv.prodCongr (ownedPairFrame S V) (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _)=
      (heldCoordinates S r V hc).trans (Equiv.prodCongr (Equiv.refl _) (heldRestCoordinates S r V hc)) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · exact (heldCoordinates_halves S r V hc x).symm
  · apply Prod.ext
    · exact (heldRestCoordinates_actual S r V hc x).symm
    · exact (heldRestCoordinates_environment S r V hc x).symm

theorem trace_environment_tensor {a b z : Type} [Fintype z] (A : Mat a) (B : Mat (b × z)) :
    partialRight ((A ⊗ₖ B).submatrix (Equiv.prodAssoc a b z) (Equiv.prodAssoc a b z))=
      A ⊗ₖ partialRight B := by
  ext i j
  change (∑ k, A i.1 j.1*B (i.2,k) (j.2,k))=A i.1 j.1*∑ k,B (i.2,k) (j.2,k)
  exact (Finset.mul_sum _ _ _).symm

def routedOwnedRaw {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (n : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    Mat (Recorder.Stock S × Registers S V) :=
  partialRight ((rawState t n).submatrix (routedFrame S (Recorder.Stock S) r V hc).symm
    (routedFrame S (Recorder.Stock S) r V hc).symm)

theorem owned_fresh_factor {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (k : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S k) :
    (routedOwnedRaw S t (k.val+1) V (activeVisits_carriers_injective S k V hV)).submatrix
      (ownedPairFrame S V).symm (ownedPairFrame S V).symm=
      pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ completeRestRecord S t k V hV := by
  let hc := activeVisits_carriers_injective S k V hV
  let P := routedFrame S (Recorder.Stock S) r V hc
  let F := ownedPairFrame S V
  let R := heldRestCoordinates S r V hc
  let C := (heldCoordinates S r V hc).trans (Equiv.prodCongr (Equiv.refl _) R)
  let B := (partialLeft (heldState S t k V hV)).submatrix R.symm R.symm
  have he : (rawState t (k.val+1)).submatrix C.symm C.symm=
      pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ B := by
    have ht : (rawState t (k.val+1)).submatrix C.symm C.symm=
        (heldState S t k V hV).submatrix (Equiv.prodCongr (Equiv.refl _) R.symm)
          (Equiv.prodCongr (Equiv.refl _) R.symm) := by
      rw [heldState_raw_coordinates]
      rfl
    rw [ht,fresh_held_pair_factor,tensor_reindex]
    rfl
  have hC : C=(P.trans (Equiv.prodCongr F (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _) :=
    (owned_fresh_route S r V hc).symm
  have ht : (rawState t (k.val+1)).submatrix (P.trans (Equiv.prodCongr F (Equiv.refl _))).symm
      (P.trans (Equiv.prodCongr F (Equiv.refl _))).symm=
      (pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ B).submatrix
        (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _) := by
    rw [hC] at he
    ext i j
    have h := congrFun₂ he ((Equiv.prodAssoc _ _ _) i) ((Equiv.prodAssoc _ _ _) j)
    simpa only [submatrix_apply,Equiv.symm_trans_apply,Equiv.symm_apply_apply] using h
  have h := congrArg partialRight ht
  rw [trace_environment_tensor] at h
  change partialRight (((rawState t (k.val+1)).submatrix P.symm P.symm).submatrix
    (Equiv.prodCongr F.symm (Equiv.refl _)) (Equiv.prodCongr F.symm (Equiv.refl _)))=_ at h
  rw [partialRight_prod_equiv] at h
  exact h

theorem completeRestRecord_from_stock {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (k : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S k) :
    partialLeft ((partialRight (rawState t (k.val+1))).submatrix
      (stockOutputPartition S V).symm (stockOutputPartition S V).symm)=
        completeRestRecord S t k V hV := by
  rw [fresh_complete_stock,partialLeft_kron]
  have he := epr_left_reduction (a := Registers S V)
  rw [registers_card] at he
  have hn : (((outputDimension S V : ℂ)⁻¹ • (1 : Mat (Registers S V)))).trace=1 := by
    rw [← he,partialLeft_trace,subset_epr_trace]
  rw [hn,one_smul]

def ownedStockRestore {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Mat (Recorder.Stock S) →ₗ[ℂ] Mat (Recorder.Stock S × Registers S V) where
  toFun A := (pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
    partialLeft (A.submatrix (stockOutputPartition S V).symm
      (stockOutputPartition S V).symm)).submatrix (ownedPairFrame S V) (ownedPairFrame S V)
  map_add' A B := by
    ext i j
    simp only [submatrix_apply,submatrix_add,kroneckerMap_apply,Matrix.add_apply,Pi.add_apply,
      partialLeft,Finset.sum_add_distrib,mul_add]
  map_smul' c A := by
    ext i j
    simp only [submatrix_apply,submatrix_smul,kroneckerMap_apply,Matrix.smul_apply,Pi.smul_apply,
      RingHom.id_apply,smul_eq_mul,partialLeft,← Finset.mul_sum]
    ring

theorem ownedStockRestore_actual {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (k : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S k) :
    ownedStockRestore S V (partialRight (rawState t (k.val+1)))=
      routedOwnedRaw S t (k.val+1) V (activeVisits_carriers_injective S k V hV) := by
  change (pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
    partialLeft ((partialRight (rawState t (k.val+1))).submatrix
      (stockOutputPartition S V).symm (stockOutputPartition S V).symm)).submatrix
        (ownedPairFrame S V) (ownedPairFrame S V)=_
  rw [completeRestRecord_from_stock S t k V hV]
  ext i j
  have h := congrFun₂ (owned_fresh_factor S t k V hV) ((ownedPairFrame S V) i) ((ownedPairFrame S V) j)
  simpa only [submatrix_apply,Equiv.symm_apply_apply] using h.symm

#print axioms ownedPairFrame
#print axioms owned_fresh_route
#print axioms trace_environment_tensor
#print axioms routedOwnedRaw
#print axioms owned_fresh_factor
#print axioms completeRestRecord_from_stock
#print axioms ownedStockRestore
#print axioms ownedStockRestore_actual
end ScheduleLaw.Blueprint
