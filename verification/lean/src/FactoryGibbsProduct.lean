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

def sumHamiltonian (H : Hamiltonian a) (K : Hamiltonian b) : Hamiltonian (a × b) :=
  ⟨H.matrix ⊗ₖ (1 : Mat b)+(1 : Mat a) ⊗ₖ K.matrix,by
    simp only [Matrix.IsHermitian,conjTranspose_add,conjTranspose_kronecker,
      conjTranspose_one,H.hermitian.eq,K.hermitian.eq]⟩

omit [Fintype a] [Fintype b] in
theorem diagonal_sum (E : a → ℂ) (F : b → ℂ) :
    diagonal E ⊗ₖ (1 : Mat b)+(1 : Mat a) ⊗ₖ diagonal F =
      diagonal (fun z : a × b => E z.1+F z.2) := by
  change diagonal E ⊗ₖ diagonal (fun _ : b => (1 : ℂ))+
    diagonal (fun _ : a => (1 : ℂ)) ⊗ₖ diagonal F = _
  rw [diagonal_kronecker_diagonal,diagonal_kronecker_diagonal,diagonal_add]
  simp only [mul_one,one_mul]

theorem sum_in_basis (H : Hamiltonian a) (K : Hamiltonian b)
    (U : Mat a) (V : Mat b) (hU : IsUnitary U) (hV : IsUnitary V)
    (E : a → ℝ) (F : b → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ))))
    (hK : K.matrix=evolve V (diagonal (fun i => (F i : ℂ)))) :
    (sumHamiltonian H K).matrix=evolve (U ⊗ₖ V)
      (diagonal (fun z : a × b => ((E z.1+F z.2 : ℝ) : ℂ))) := by
  have hd : diagonal (fun z : a × b => ((E z.1+F z.2 : ℝ) : ℂ)) =
      diagonal (fun i => (E i : ℂ)) ⊗ₖ (1 : Mat b)+
        (1 : Mat a) ⊗ₖ diagonal (fun j => (F j : ℂ)) := by
    rw [diagonal_sum]
    simp only [Complex.ofReal_add]
  rw [hd]
  simp only [sumHamiltonian,evolve,conjTranspose_kronecker,mul_add,add_mul,
    ← mul_kronecker_mul,mul_one,hU.2,hV.2]
  rw [hH,hK]
  rfl

theorem gibbs_product (β : ℝ) (H : Hamiltonian a) (K : Hamiltonian b) :
    gibbs β (sumHamiltonian H K)=gibbs β H ⊗ₖ gibbs β K := by
  let U : Mat a := H.hermitian.eigenvectorUnitary
  let V : Mat b := K.hermitian.eigenvectorUnitary
  let E := H.hermitian.eigenvalues
  let F := K.hermitian.eigenvalues
  have hU : IsUnitary U := H.hermitian.eigenvectorUnitary.property
  have hV : IsUnitary V := K.hermitian.eigenvectorUnitary.property
  have hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ))) := H.hermitian.spectral_theorem
  have hK : K.matrix=evolve V (diagonal (fun i => (F i : ℂ))) := K.hermitian.spectral_theorem
  rw [gibbs_in_basis β (sumHamiltonian H K) (U ⊗ₖ V) (unitary_kron hU hV) _
    (sum_in_basis H K U V hU hV E F hH hK),gibbs_in_basis β H U hU E hH,
    gibbs_in_basis β K V hV F hK]
  have hexp (z : a × b) : Real.exp (-β*(E z.1+F z.2))=
      Real.exp (-β*E z.1)*Real.exp (-β*F z.2) := by rw [mul_add,Real.exp_add]
  have hz : (∑ z : a × b,Real.exp (-β*(E z.1+F z.2))) =
      (∑ i,Real.exp (-β*E i))*(∑ j,Real.exp (-β*F j)) := by
    simp only [hexp,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  have hd : diagonal (fun z : a × b =>
      ((Real.exp (-β*(E z.1+F z.2))/(∑ z : a × b,Real.exp (-β*(E z.1+F z.2))) : ℝ) : ℂ)) =
      diagonal (fun i => ((Real.exp (-β*E i)/(∑ j,Real.exp (-β*E j)) : ℝ) : ℂ)) ⊗ₖ
        diagonal (fun i => ((Real.exp (-β*F i)/(∑ j,Real.exp (-β*F j)) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]
    congr 1
    funext z
    rw [hexp,hz]
    simp only [← Complex.ofReal_mul]
    congr 1
    exact (div_mul_div_comm _ _ _ _).symm
  rw [hd]
  simp only [evolve,conjTranspose_kronecker,← mul_kronecker_mul]

end ScheduleLaw.Blueprint.FactoryGibbs
