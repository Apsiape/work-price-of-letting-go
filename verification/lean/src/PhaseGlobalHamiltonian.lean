import PhasePayloadHamiltonian
import PhaseLocalPlacement
import FactoryPhysicalHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseGlobalHamiltonian
open History PhaseLocalHamiltonian
variable {p : Type} [Fintype p] [DecidableEq p]

theorem total (I : Inventory) {b N : ℕ} (A : Finset (Fin I.count))
    (e : Fin N ≃ Fin b × p) (H : Mat (Fin b)) (K : Mat p) :
    (H ⊗ₖ (1 : Mat p)+(1 : Mat (Fin b)) ⊗ₖ K).submatrix e e ⊗ₖ (1 : Mat (Payload I))+
      (1 : Mat (Fin N)) ⊗ₖ payloadHamiltonian I=
    (((H ⊗ₖ (1 : Mat (Restricted I A))+(1 : Mat (Fin b)) ⊗ₖ (restricted I A).matrix) ⊗ₖ
      (1 : Mat p)+(1 : Mat (Fin b × Restricted I A)) ⊗ₖ K) ⊗ₖ
        (1 : Mat (Restricted I Aᶜ))+
      (1 : Mat ((Fin b × Restricted I A) × p)) ⊗ₖ (restricted I Aᶜ).matrix).submatrix
        (PhaseLocalPlacement.frame I A e) (PhaseLocalPlacement.frame I A e) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨x,z⟩,rfl⟩ := e.symm.surjective i
  obtain ⟨⟨y,z'⟩,rfl⟩ := e.symm.surjective j
  have ht := congrFun (congrFun (PhasePayloadHamiltonian.total I b A H) (x,u)) (y,v)
  have hp : (1 : Mat (Payload I)) u v=
      (1 : Mat (Restricted I A)) (restrictPayload I A u) (restrictPayload I A v)*
        (1 : Mat (Restricted I Aᶜ)) (restrictPayload I Aᶜ u) (restrictPayload I Aᶜ v) := by
    change (if u=v then 1 else 0)=
      (if restrictPayload I A u=restrictPayload I A v then 1 else 0)*
        (if restrictPayload I Aᶜ u=restrictPayload I Aᶜ v then 1 else 0)
    have hh : u=v ↔ restrictPayload I A u=restrictPayload I A v ∧
        restrictPayload I Aᶜ u=restrictPayload I Aᶜ v := by
      constructor
      · intro h; exact ⟨congrArg (restrictPayload I A) h,congrArg (restrictPayload I Aᶜ) h⟩
      · rintro ⟨h1,h2⟩; exact (payloadPartition I A).injective (Prod.ext h1 h2)
    simp only [hh]
    by_cases h1 : restrictPayload I A u=restrictPayload I A v <;>
      by_cases h2 : restrictPayload I Aᶜ u=restrictPayload I Aᶜ v <;> simp [h1,h2]

  change H x y*(1 : Mat (Payload I)) u v+(1 : Mat (Fin b)) x y*(payloadHamiltonian I) u v=
    ((H x y*(1 : Mat (Restricted I A)) (restrictPayload I A u) (restrictPayload I A v)+
      (1 : Mat (Fin b)) x y*(restricted I A).matrix (restrictPayload I A u) (restrictPayload I A v))*
        (1 : Mat (Restricted I Aᶜ)) (restrictPayload I Aᶜ u) (restrictPayload I Aᶜ v))+
    (1 : Mat (Fin b × Restricted I A)) (x,restrictPayload I A u) (y,restrictPayload I A v)*
      (restricted I Aᶜ).matrix (restrictPayload I Aᶜ u) (restrictPayload I Aᶜ v) at ht
  simp only [submatrix_apply,kroneckerMap_apply,Matrix.add_apply,PhaseLocalPlacement.frame,
    Equiv.coe_fn_mk,Equiv.apply_symm_apply,FactoryPhysicalHamiltonian.one_prod,
    Matrix.one_apply,e.symm.injective.eq_iff,Prod.mk.injEq,FactoryPhysicalHamiltonian.indicator_and] at *
  rw [hp] at ht ⊢
  linear_combination ht*(if z=z' then (1 : ℂ) else 0)

end ScheduleLaw.Blueprint.PhaseGlobalHamiltonian
