import FactoryEnergyTransport
import FactoryTensorPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryBatchSpectrum
open History

def index (d m : ℕ) : (Fin m → Fin d) ≃ Fin (Fintype.card (Fin m → Fin d)) := Fintype.equivFin _

def hamiltonian {d : ℕ} (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    Hamiltonian (Fin (Fintype.card (Fin m → Fin d))) :=
  FactoryGibbs.reindexHamiltonian (index d m).symm
    (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) m)

theorem physical {d : ℕ} (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    (hamiltonian β q m).matrix.submatrix (index d m) (index d m)=
      tensorHamiltonian (tangentHamiltonian β q) m := by
  ext i j
  simp only [hamiltonian,FactoryGibbs.reindexHamiltonian,submatrix_apply,
    Equiv.symm_apply_apply,FactoryTensor.hamiltonian,FactoryGibbs.tangent]

theorem partition_one {d : ℕ} (β : ℝ) (hβ : β≠0) (q : Density (Fin d))
    (hq : q.matrix.PosDef) (m : ℕ) : partition β (hamiltonian β q m)=1 := by
  rw [hamiltonian,FactoryGibbs.partition_reindex]
  exact FactoryTensor.tangent_partition_tensor β hβ q hq m

theorem norm_bound {d : ℕ} (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    ‖(hamiltonian β q m).matrix‖ ≤ (m : ℝ)*
      (∑ i,|(FactoryGibbs.tangent β q).hermitian.eigenvalues i|) := by
  rw [hamiltonian,FactoryGibbs.reindexHamiltonian,FactoryEnergyTransport.norm_reindex]
  exact FactoryEnergy.tensor_norm_bound (FactoryGibbs.tangent β q) m

end ScheduleLaw.Blueprint.FactoryBatchSpectrum
