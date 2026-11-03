import FactoryGibbs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryGibbs
open History

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def reindexHamiltonian (e : a ≃ b) (H : Hamiltonian b) : Hamiltonian a :=
  ⟨H.matrix.submatrix e e,H.hermitian.submatrix e⟩

theorem cfc_reindex (e : a ≃ b) (H : Hamiltonian b) (f : ℝ → ℝ) (hf : Continuous f) :
    (reindexHamiltonian e H).hermitian.cfc f=(H.hermitian.cfc f).submatrix e e := by
  letI := matrixCStarStructure a
  letI := matrixCStarStructure b
  rw [← Matrix.IsHermitian.cfc_eq,← Matrix.IsHermitian.cfc_eq]
  exact (StarAlgHomClass.map_cfc (matrixReindexStarEquiv e.symm) f H.matrix
    (hf := hf.continuousOn)
    (hφ := (matrixReindexStarEquiv e.symm).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := H.hermitian) (hφa := (reindexHamiltonian e H).hermitian)).symm

theorem partition_reindex (e : a ≃ b) (β : ℝ) (H : Hamiltonian b) :
    partition β (reindexHamiltonian e H)=partition β H := by
  have ht := congrArg Matrix.trace (cfc_reindex e H (fun x => Real.exp (-β*x)) (by fun_prop))
  rw [submatrix_trace_equiv] at ht
  unfold Matrix.IsHermitian.cfc at ht
  rw [trace_unitary_conjugation,trace_unitary_conjugation] at ht
  have hr := congrArg Complex.re ht
  simpa only [partition,trace_diagonal,Function.comp_apply,Complex.re_sum,
    Complex.ofReal_re] using hr

theorem gibbs_reindex (e : a ≃ b) (β : ℝ) (H : Hamiltonian b) :
    gibbs β (reindexHamiltonian e H)=(gibbs β H).submatrix e e := by
  change (reindexHamiltonian e H).hermitian.cfc
    (fun x => Real.exp (-β*x)/partition β (reindexHamiltonian e H)) =
      (H.hermitian.cfc (fun x => Real.exp (-β*x)/partition β H)).submatrix e e
  rw [partition_reindex]
  exact cfc_reindex e H _ (by fun_prop)

end ScheduleLaw.Blueprint.FactoryGibbs
