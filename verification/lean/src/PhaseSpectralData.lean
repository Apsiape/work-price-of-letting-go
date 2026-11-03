import PhaseSpectralHardware
import PhaseSpectralAccuracy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhaseSpectralData
open History PhaseSpectralLabels PhaseSpectralHardware PhaseGateDilation
variable {I : Inventory} {S : Schedule I} {β : ℝ}

theorem local_card_pos (p : Driven S β) (k : Cut S) : 0<Fintype.card (Local p k) := by
  letI : Nonempty (Fin p.extension.b) := ⟨⟨0,p.extension.b_pos⟩⟩
  letI : Nonempty (Restricted I (held S k)) := ⟨fun c => ⟨0,I.dim_pos c.val⟩⟩
  exact Fintype.card_pos

def cutConstant (p : Driven S β) (k : Cut S) : ℝ :=
  (Fintype.card (Local p k) : ℝ)*((Fintype.card (Index p) : ℝ)+1)*Real.pi*
    ‖((basis (hamiltonian p k))ᴴ : Mat (Local p k))‖

def constant (p : Driven S β) : ℝ := ∑ k : Cut S,cutConstant p k

theorem cut_nonneg (p : Driven S β) (k : Cut S) : 0≤cutConstant p k := by
  dsimp only [cutConstant]
  positivity

theorem constant_nonneg (p : Driven S β) : 0≤constant p :=
  Finset.sum_nonneg (fun k _ => cut_nonneg p k)

theorem cut_error (p : Driven S β) (L : ℕ) (hL : 0<L) (k : Cut S) :
    ‖(localGate p L k*PhasePacketMap.embed (PhasePacketDensity.packet L)-
      PhasePacketMap.embed (PhasePacketDensity.packet L)*localContactGate p.extension k :
        Matrix (Local p k × Phase p L) (Local p k) ℂ)‖≤cutConstant p k/(L+1 : ℝ) := by
  have h := PhaseSpectralAccuracy.error_bound (hamiltonian p k) (localContactGate p.extension k)
    (PhaseVectorDistance.unitary_instances _ _ _ (localContactGate_spec p.extension k).1)
    (labels p k) (labels_bounds p k) L hL (local_card_pos p k)
  apply h.trans
  dsimp only [cutConstant]
  exact le_of_eq (by ring)

theorem dim (p : Driven S β) (L : ℕ) : D p L=(L+4)^Fintype.card (Index p) := by
  exact (Fintype.card_coe _).trans (PhaseLatticeBox.box_card L)

theorem controllerPhase_matrix (p : Driven S β) (L : ℕ) (hL : 0<L) :
    (controllerPhase p L hL).matrix=
      (pureMatrix (PhasePacketDensity.packet (ι:=Index p) L)).submatrix
        (Fintype.equivFin (Phase p L)).symm (Fintype.equivFin (Phase p L)).symm := by
  change (PhasePacketDensity.density L hL).matrix.submatrix _ _=_
  rw [PhasePacketDensity.matrix]

end ScheduleLaw.Blueprint.PhaseSpectralData
