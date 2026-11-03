import PhaseSpectralHardware
import PhaseGlobalHamiltonian
import PhaseHardwareEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseSpectralConservation
open History PhaseSpectralHardware PhaseSpectralLabels PhaseLocalHamiltonian
variable {I : Inventory} {S : Schedule I} {β : ℝ}

theorem body_energy (p : Driven S β) (L : ℕ) (hL : 0<L) :
    (hardware p L hL).bodyHamiltonian=
      (p.bodyHamiltonian ⊗ₖ (1 : Mat (Phase p L))+
        (1 : Mat (Fin p.extension.b)) ⊗ₖ (phaseH p L).matrix).submatrix
          (frame p L) (frame p L) := by
  have h := PhaseHardwareEnergy.physical p (dim_pos p L) (controllerPhase p L hL)
    (phaseHFin p L) (G p L) (G_unitary p L) (G_local p L)
  change (hardware p L hL).bodyHamiltonian=_ at h
  rw [h]
  ext i j
  simp only [submatrix_apply,kroneckerMap_apply,Matrix.add_apply,phaseHFin,
    FactoryGibbs.reindexHamiltonian,frame,Equiv.trans_apply,Equiv.prodCongr_apply,
    Prod.map_apply,Equiv.refl_apply,Matrix.one_apply,
    (Fintype.equivFin (Phase p L)).symm.injective.eq_iff]
  dsimp only [Prod.map,Equiv.refl]
  simp only [Equiv.coe_fn_mk,(Fintype.equivFin (Phase p L)).symm.injective.eq_iff] <;> rfl

theorem conserving (p : Driven S β) (L : ℕ) (hL : 0<L) (k : Cut S) :
    Conserves ((hardware p L hL).extension.gate k)
      ((hardware p L hL).bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+
        (1 : Mat (Fin (hardware p L hL).extension.b)) ⊗ₖ payloadHamiltonian I) := by
  rw [body_energy]
  change Conserves (G p L k) _
  rw [PhaseGlobalHamiltonian.total I (held S k) (frame p L) p.bodyHamiltonian (phaseH p L).matrix]
  exact PhaseLocalPlacement.conserving I (held S k) (frame p L) (localGate p L k)
    ((hamiltonian p k).matrix ⊗ₖ (1 : Mat (Phase p L))+
      (1 : Mat (Local p k)) ⊗ₖ (phaseH p L).matrix)
    (restricted I (held S k)ᶜ).matrix
    (PhaseVectorDistance.unitary_instances _ _ _ (localGate_unitary p L k)) (localGate_conserving p L k)

def engine (p : Driven S β) (L : ℕ) (hL : 0<L) : Engine S β :=
  PhaseHardware.toEngine (hardware p L hL) (conserving p L hL)

theorem engine_hardware (p : Driven S β) (L : ℕ) (hL : 0<L) :
    (engine p L hL).extension=(hardware p L hL).extension := rfl

end ScheduleLaw.Blueprint.PhaseSpectralConservation
