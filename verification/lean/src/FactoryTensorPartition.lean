import FactoryLedger
import FactoryTensorStock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryTensor
open History FactoryGibbs FiniteResidue

theorem tangent_partition_tensor {d : ℕ} (β : ℝ) (hβ : β≠0)
    (q : Density (Fin d)) (hq : q.matrix.PosDef) (m : ℕ) :
    partition β (hamiltonian (tangent β q) m)=1 := by
  rw [tensor_partition,FactoryLedger.tangent_partition β hβ q hq,one_pow]

end ScheduleLaw.Blueprint.FactoryTensor
