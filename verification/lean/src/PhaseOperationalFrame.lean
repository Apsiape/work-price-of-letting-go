import PhaseLocalPlacement
import PhasePacketMixed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseOperationalFrame
open History
variable {p : Type} [Fintype p] [DecidableEq p]

abbrev Local (I : Inventory) (b : ℕ) (A : Finset (Fin I.count)) := Fin b × Restricted I A
abbrev Env (I : Inventory) (r : ℕ) (A : Finset (Fin I.count)) := Restricted I Aᶜ × Fin r

def old (I : Inventory) (b r : ℕ) (A : Finset (Fin I.count)) :
    (Fin b × (Payload I × Fin r)) ≃ Local I b A × Env I r A where
  toFun x := ((x.1,restrictPayload I A x.2.1),(restrictPayload I Aᶜ x.2.1,x.2.2))
  invFun x := (x.1.1,((payloadPartition I A).symm (x.1.2,x.2.1),x.2.2))
  left_inv x := by
    have h := (payloadPartition I A).symm_apply_apply x.2.1
    change (x.1,((payloadPartition I A).symm ((payloadPartition I A) x.2.1),x.2.2))=x
    rw [h]
  right_inv x := by
    have h := (payloadPartition I A).apply_symm_apply (x.1.2,x.2.1)
    change ((x.1.1,((payloadPartition I A) ((payloadPartition I A).symm (x.1.2,x.2.1))).1),
      (((payloadPartition I A) ((payloadPartition I A).symm (x.1.2,x.2.1))).2,x.2.2))=x
    rw [h]

def global (I : Inventory) {b N : ℕ} (r : ℕ) (e : Fin N ≃ Fin b × p) :
    (Fin N × (Payload I × Fin r)) ≃ (Fin b × (Payload I × Fin r)) × p where
  toFun x := (((e x.1).1,x.2),(e x.1).2)
  invFun x := (e.symm (x.1.1,x.2),x.1.2)
  left_inv x := by change (e.symm (e x.1),x.2)=x; rw [e.symm_apply_apply]
  right_inv x := by
    change (((e (e.symm (x.1.1,x.2))).1,x.1.2),(e (e.symm (x.1.1,x.2))).2)=x
    rw [e.apply_symm_apply]

def contactFrame (I : Inventory) {b N : ℕ} (r : ℕ) (A : Finset (Fin I.count))
    (e : Fin N ≃ Fin b × p) :
    (Fin N × (Payload I × Fin r)) ≃ (Local I b A × p) × Env I r A where
  toFun x := ((((e x.1).1,restrictPayload I A x.2.1),(e x.1).2),
    (restrictPayload I Aᶜ x.2.1,x.2.2))
  invFun x := (e.symm (x.1.1.1,x.1.2),((payloadPartition I A).symm (x.1.1.2,x.2.1),x.2.2))
  left_inv x := by
    apply Prod.ext
    · exact e.symm_apply_apply x.1
    · exact Prod.ext ((payloadPartition I A).symm_apply_apply x.2.1) rfl
  right_inv x := by
    have he := e.apply_symm_apply (x.1.1.1,x.1.2)
    have hp := (payloadPartition I A).apply_symm_apply (x.1.1.2,x.2.1)
    change ((((e (e.symm (x.1.1.1,x.1.2))).1,
      ((payloadPartition I A) ((payloadPartition I A).symm (x.1.1.2,x.2.1))).1),
      (e (e.symm (x.1.1.1,x.1.2))).2),
      (((payloadPartition I A) ((payloadPartition I A).symm (x.1.1.2,x.2.1))).2,x.2.2))=x
    rw [he,hp]

theorem factor (I : Inventory) {b N : ℕ} (r : ℕ) (A : Finset (Fin I.count))
    (e : Fin N ≃ Fin b × p) (ρ : Mat (Fin b × (Payload I × Fin r))) (v : p → ℂ) :
    (((ρ ⊗ₖ pureMatrix v).submatrix (global I r e) (global I r e)).submatrix
      (contactFrame I r A e).symm (contactFrame I r A e).symm)=
    PhasePacketMixed.attach v (ρ.submatrix (old I b r A).symm (old I b r A).symm) := by
  ext i j
  simp only [submatrix_apply,contactFrame,global,old,PhasePacketMixed.attach,
    PhasePacketReference.wires,Equiv.symm_mk,Equiv.coe_fn_mk,Equiv.apply_symm_apply,kroneckerMap_apply] <;> rfl

theorem device (I : Inventory) {b N : ℕ} (r : ℕ) (A : Finset (Fin I.count))
    (e : Fin N ≃ Fin b × p) (V : Mat (Local I b A × p)) :
    (fun i j : Fin N × (Payload I × Fin r) =>
      PhaseLocalPlacement.gate I A e V (i.1,i.2.1) (j.1,j.2.1)*
        (if i.2.2=j.2.2 then 1 else 0))=
      (V ⊗ₖ (1 : Mat (Env I r A))).submatrix (contactFrame I r A e) (contactFrame I r A e) := by
  ext i j
  simp only [PhaseLocalPlacement.gate,FactoryPlacement.place,submatrix_apply,
    PhaseLocalPlacement.frame,Equiv.coe_fn_mk,kroneckerMap_apply,Matrix.one_apply,
    contactFrame,global,old,Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_apply,
    PhasePacketReference.wires,Prod.mk.injEq]
  by_cases h : restrictPayload I Aᶜ i.2.1=restrictPayload I Aᶜ j.2.1 <;>
    by_cases hm : i.2.2=j.2.2 <;> simp [h,hm]

theorem old_device (I : Inventory) (b r : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Local I b A)) (M : Mat (Fin b × Payload I))
    (h : ∀ i j,M i j=U (i.1,restrictPayload I A i.2) (j.1,restrictPayload I A j.2)*
      (if restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 then 1 else 0)) :
    (fun i j : Fin b × (Payload I × Fin r) => M (i.1,i.2.1) (j.1,j.2.1)*
      (if i.2.2=j.2.2 then 1 else 0))=FactoryPlacement.place (old I b r A) U := by
  ext i j
  change M (i.1,i.2.1) (j.1,j.2.1)*(if i.2.2=j.2.2 then 1 else 0)=
    U (i.1,restrictPayload I A i.2.1) (j.1,restrictPayload I A j.2.1)*
      (if (restrictPayload I Aᶜ i.2.1,i.2.2)=(restrictPayload I Aᶜ j.2.1,j.2.2) then 1 else 0)
  rw [h]
  simp only [Prod.mk.injEq]
  by_cases hp : restrictPayload I Aᶜ i.2.1=restrictPayload I Aᶜ j.2.1 <;>
    by_cases hm : i.2.2=j.2.2 <;> simp [hp,hm]

end ScheduleLaw.Blueprint.PhaseOperationalFrame
