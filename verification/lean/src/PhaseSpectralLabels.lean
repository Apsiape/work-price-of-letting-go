import PhaseLocalHamiltonian
import PhaseSpectralTransport
import PhasePacketDensity
import PhaseLocalPlacement

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseSpectralLabels
open History PhaseLatticeBox PhaseGateDilation
variable {I : Inventory} {S : Schedule I} {β : ℝ}

abbrev Local (p : Driven S β) (k : Cut S) := Fin p.extension.b × Restricted I (held S k)
abbrev Index (p : Driven S β) := Sigma (Local p)

def hamiltonian (p : Driven S β) (k : Cut S) : Hamiltonian (Local p k) :=
  PhaseLocalHamiltonian.localH p (held S k)

def weights (p : Driven S β) (x : Index p) : ℝ := energies (hamiltonian p x.1) x.2

def labels (p : Driven S β) (k : Cut S) (i : Local p k) : PhaseLatticeBox.Lattice (Index p) :=
  label (Sigma.mk k i)

def ω (p : Driven S β) : PhaseLatticeBox.Lattice (Index p) →+ ℝ := frequency (weights p)

theorem label_energy (p : Driven S β) (k : Cut S) (i : Local p k) :
    ω p (labels p k i)=energies (hamiltonian p k) i := frequency_label _ _

theorem labels_bounds (p : Driven S β) (k : Cut S) (i : Local p k) (j : Index p) :
    0≤labels p k i j ∧ labels p k i j≤1 := by
  simp only [labels,label]
  split_ifs <;> norm_num

abbrev Phase (p : Driven S β) (L : ℕ) := ↥(box (Index p) L)

def phaseH (p : Driven S β) (L : ℕ) : Hamiltonian (Phase p L) :=
  FlatMatrix.diagonalHamiltonian (Phase p L) (fun x => ω p x.val)

def localGate (p : Driven S β) (L : ℕ) (k : Cut S) : Mat (Local p k × Phase p L) :=
  evolve (basis (hamiltonian p k) ⊗ₖ (1 : Mat (Phase p L)))
    (FinitePhaseShell.gate (labels p k) (box (Index p) L)
      (inBasis (hamiltonian p k) (localContactGate p.extension k)))

theorem localGate_unitary (p : Driven S β) (L : ℕ) (k : Cut S) : IsUnitary (localGate p L k) := by
  have hU : IsUnitary (inBasis (hamiltonian p k) (localContactGate p.extension k)) :=
    conjugate_unitary _ _ (localContactGate_spec p.extension k).1
      (adjoint_unitary _ (basis_unitary (hamiltonian p k)))
  have hs := FinitePhaseShell.unitary (labels p k) (box (Index p) L) _ hU
  have h1 : IsUnitary (1 : Mat (Phase p L)) := by constructor <;> simp
  exact conjugate_unitary _ _ (PhaseVectorDistance.unitary_instances _ _ _ hs)
    (PhaseVectorDistance.unitary_instances _ _ _ (unitary_kron (basis_unitary (hamiltonian p k)) h1))

theorem localGate_conserving (p : Driven S β) (L : ℕ) (k : Cut S) :
    Conserves (localGate p L k)
      ((hamiltonian p k).matrix ⊗ₖ (1 : Mat (Phase p L))+
        (1 : Mat (Local p k)) ⊗ₖ (phaseH p L).matrix) :=
  PhaseSpectralTransport.labeled_conserving _ _ (localContactGate_spec p.extension k).1
    _ _ _ (label_energy p k)

end ScheduleLaw.Blueprint.PhaseSpectralLabels
