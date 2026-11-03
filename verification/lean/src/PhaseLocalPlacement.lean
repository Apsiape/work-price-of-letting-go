import CacheServiceGates
import FactoryPlacement

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseLocalPlacement

variable {p : Type} [Fintype p] [DecidableEq p]

def frame (I : Inventory) {b N : ℕ} (A : Finset (Fin I.count))
    (e : Fin N ≃ Fin b × p) :
    Fin N × Payload I ≃ ((Fin b × Restricted I A) × p) × Restricted I Aᶜ where
  toFun x := ((((e x.1).1,restrictPayload I A x.2),(e x.1).2),restrictPayload I Aᶜ x.2)
  invFun x := (e.symm (x.1.1.1,x.1.2),(payloadPartition I A).symm (x.1.1.2,x.2))
  left_inv x := by
    apply Prod.ext
    · exact e.symm_apply_apply x.1
    · exact (payloadPartition I A).symm_apply_apply x.2
  right_inv x := by
    have he := e.apply_symm_apply (x.1.1.1,x.1.2)
    have hp := (payloadPartition I A).apply_symm_apply (x.1.1.2,x.2)
    change ((((e (e.symm (x.1.1.1,x.1.2))).1,
      ((payloadPartition I A) ((payloadPartition I A).symm (x.1.1.2,x.2))).1),
      (e (e.symm (x.1.1.1,x.1.2))).2),
      ((payloadPartition I A) ((payloadPartition I A).symm (x.1.1.2,x.2))).2)=x
    rw [he,hp]

def gate (I : Inventory) {b N : ℕ} (A : Finset (Fin I.count)) (e : Fin N ≃ Fin b × p)
    (V : Mat ((Fin b × Restricted I A) × p)) : Mat (Fin N × Payload I) :=
  FactoryPlacement.place (frame I A e) V

theorem unitary (I : Inventory) {b N : ℕ} (A : Finset (Fin I.count)) (e : Fin N ≃ Fin b × p)
    (V : Mat ((Fin b × Restricted I A) × p)) (hV : IsUnitary V) : IsUnitary (gate I A e V) :=
  unitary_submatrix (frame I A e) (unitary_kron hV (by constructor <;> simp))

/-- The phase is body workspace; the placed gate acts only on the held
carriers, without reading or controlling on any unheld carrier. -/
theorem local_on (I : Inventory) {b N : ℕ} (A : Finset (Fin I.count)) (e : Fin N ≃ Fin b × p)
    (V : Mat ((Fin b × Restricted I A) × p)) (hV : IsUnitary V) : LocalOn I N A (gate I A e V) := by
  let E := CacheServiceGates.wires e (Restricted I A)
  refine ⟨V.submatrix E E,unitary_submatrix E hV,?_⟩
  intro i j
  simp only [gate,FactoryPlacement.place,submatrix_apply,frame,Equiv.coe_fn_mk,
    kroneckerMap_apply,Matrix.one_apply,E,CacheServiceGates.wires]

theorem conserving (I : Inventory) {b N : ℕ} (A : Finset (Fin I.count)) (e : Fin N ≃ Fin b × p)
    (V H : Mat ((Fin b × Restricted I A) × p)) (K : Mat (Restricted I Aᶜ))
    (hV : IsUnitary V) (hH : Conserves V H) :
    Conserves (gate I A e V)
      ((H ⊗ₖ (1 : Mat (Restricted I Aᶜ))+(1 : Mat ((Fin b × Restricted I A) × p)) ⊗ₖ K).submatrix
        (frame I A e) (frame I A e)) :=
  FactoryPlacement.conserves (frame I A e) V H K hV hH

end ScheduleLaw.Blueprint.PhaseLocalPlacement
