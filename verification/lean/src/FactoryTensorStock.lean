import FactoryTensorHamiltonian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryTensor
open History FiniteResidue

theorem tensor_partition {d : ℕ} (β : ℝ) (H : Hamiltonian (Fin d)) (m : ℕ) :
    partition β (hamiltonian H m)=(partition β H)^m := by
  let U : Mat (Fin d) := H.hermitian.eigenvectorUnitary
  let E := H.hermitian.eigenvalues
  have hU : IsUnitary U := H.hermitian.eigenvectorUnitary.property
  have hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ))) := H.hermitian.spectral_theorem
  rw [FactoryGibbs.partition_in_basis β (hamiltonian H m) (tensorMatrix U m)
    (tensorMatrix_unitary U hU m) _ (tensorHamiltonian_in_basis H.matrix U hU E hH m)]
  have hexp (u : Fin m → Fin d) : Real.exp (-β*∑ k,E (u k))=∏ k,Real.exp (-β*E (u k)) := by
    rw [Finset.mul_sum,Real.exp_sum]
  simp only [hexp]
  rw [← Fintype.prod_sum (fun (_ : Fin m) j => Real.exp (-β*E j))]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rfl

theorem tangent_batch {d : ℕ} (β : ℝ) (hβ : β≠0) (q : Density (Fin d))
    (hq : q.matrix.PosDef) (m : ℕ) :
    gibbs β (hamiltonian (FactoryGibbs.tangent β q) m)=tensorPower q.matrix m := by
  rw [gibbs_tensor,FactoryGibbs.tangent_gibbs β hβ q hq]
  rfl

/-- The declared physical batch and independent auxiliary stock use the
 literal reservoir Hamiltonian required by Formation. -/
theorem batch_aux_stock {d : ℕ} {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (hβ : β≠0) (q : Density (Fin d)) (hq : q.matrix.PosDef) (m : ℕ)
    (HA : Hamiltonian a) :
    gibbs β (FactoryGibbs.sumHamiltonian (hamiltonian (FactoryGibbs.tangent β q) m) HA) =
      tensorPower q.matrix m ⊗ₖ gibbs β HA := by
  rw [FactoryGibbs.gibbs_product,tangent_batch β hβ q hq]

end ScheduleLaw.Blueprint.FactoryTensor
