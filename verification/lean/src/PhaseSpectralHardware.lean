import PhaseSpectralLabels
import PhaseHardware

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseSpectralHardware
open History PhaseLatticeBox PhaseSpectralLabels
variable {I : Inventory} {S : Schedule I} {β : ℝ}

abbrev D (p : Driven S β) (L : ℕ) := Fintype.card (Phase p L)

theorem dim_pos (p : Driven S β) (L : ℕ) : 0<D p L := by
  letI : Nonempty (Phase p L) := ⟨⟨0,(box_mem _ _).mpr (fun _ => by change -2≤(0 : ℤ) ∧ (0 : ℤ)≤(L : ℤ)+1; constructor <;> omega)⟩⟩
  exact Fintype.card_pos

def frame (p : Driven S β) (L : ℕ) : Fin (p.extension.b*D p L) ≃ Fin p.extension.b × Phase p L :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin (Phase p L)).symm)

def G (p : Driven S β) (L : ℕ) (k : Cut S) : Mat (Fin (p.extension.b*D p L) × Payload I) :=
  PhaseLocalPlacement.gate I (held S k) (frame p L) (localGate p L k)

theorem G_unitary (p : Driven S β) (L : ℕ) (k : Cut S) : IsUnitary (G p L k) :=
  PhaseLocalPlacement.unitary _ _ _ _ (PhaseVectorDistance.unitary_instances _ _ _ (localGate_unitary p L k))

theorem G_local (p : Driven S β) (L : ℕ) (k : Cut S) :
    LocalOn I (p.extension.b*D p L) (held S k) (G p L k) :=
  PhaseLocalPlacement.local_on _ _ _ _ (PhaseVectorDistance.unitary_instances _ _ _ (localGate_unitary p L k))

def controllerPhase (p : Driven S β) (L : ℕ) (hL : 0<L) : Density (Fin (D p L)) :=
  let φ := PhasePacketDensity.density (ι:=Index p) L hL
  ⟨φ.matrix.submatrix (Fintype.equivFin (Phase p L)).symm (Fintype.equivFin (Phase p L)).symm,
    φ.positive.submatrix _,by rw [submatrix_trace_equiv]; exact φ.normalized⟩

def phaseHFin (p : Driven S β) (L : ℕ) : Hamiltonian (Fin (D p L)) :=
  FactoryGibbs.reindexHamiltonian (Fintype.equivFin (Phase p L)).symm (phaseH p L)

/-- One specified finite hardware for all coherent testers: the old
battery and every thermal stock, plus the fully charged common phase. -/
def hardware (p : Driven S β) (L : ℕ) (hL : 0<L) : Driven S β :=
  PhaseHardware.hardware p (dim_pos p L) (controllerPhase p L hL) (phaseHFin p L)
    (G p L) (G_unitary p L) (G_local p L)

theorem capital_charged (p : Driven S β) (L : ℕ) (hL : 0<L) :
    Driven.CapitalCharged (hardware p L hL) := le_rfl

theorem nominal_debit (p : Driven S β) (L : ℕ) (hL : 0<L) :
    Driven.nominalDebit (hardware p L hL)=Driven.nominalDebit p := rfl

end ScheduleLaw.Blueprint.PhaseSpectralHardware
