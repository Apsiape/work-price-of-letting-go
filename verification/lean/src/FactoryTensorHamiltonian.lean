import FactoryGibbsProduct
import FiniteTensorMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryTensor
open History FiniteResidue

variable {d : ℕ}

def family {m : ℕ} (A : Fin m → Mat (Fin d)) : Mat (Fin m → (Fin d)) := fun u v => ∏ k,A k (u k) (v k)

theorem family_mul {m : ℕ} (A B : Fin m → Mat (Fin d)) :
    family (fun k => A k*B k) = family A*family B := by
  ext u v
  change (∏ i, ∑ j, A i (u i) j * B i j (v i)) =
    ∑ w : Fin m → (Fin d), (∏ i, A i (u i) (w i)) * (∏ i, B i (w i) (v i))
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.prod_mul_distrib

theorem family_star {m : ℕ} (A : Fin m → Mat (Fin d)) :
    family (fun k => (A k)ᴴ) = (family A)ᴴ := by
  ext u v
  simp [family,Matrix.conjTranspose_apply]

theorem family_evolve {m : ℕ} (U A : Fin m → Mat (Fin d)) :
    evolve (family U) (family A) = family (fun k => evolve (U k) (A k)) := by
  simp only [evolve,← family_star,← family_mul]

theorem family_diagonal {m : ℕ} (p : Fin m → (Fin d) → ℂ) :
    family (fun k => diagonal (p k)) = diagonal (fun u => ∏ k,p k (u k)) := by
  ext u v
  by_cases huv : u=v
  · subst v; simp [family]
  · obtain ⟨i,hi⟩ : ∃ i,u i≠v i := by
      by_contra h; push Not at h; exact huv (funext h)
    change (∏ j, (diagonal (p j)) (u j) (v j)) = _
    rw [Matrix.diagonal_apply_ne _ huv]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem single_entry {m : ℕ} (A : Mat (Fin d)) (k : Fin m) (u v : Fin m → (Fin d)) :
    family (fun j => if j=k then A else (1 : Mat (Fin d))) u v =
      A (u k) (v k) * if ∀ j,j≠k → u j=v j then 1 else 0 := by
  by_cases hrest : ∀ j,j≠k → u j=v j
  · have he (j : Fin m) : (if j=k then A else (1 : Mat (Fin d))) (u j) (v j) =
        if j=k then A (u k) (v k) else 1 := by
      by_cases hj : j=k
      · subst j; simp
      · simp [hj,Matrix.one_apply,hrest j hj]
    rw [if_pos hrest,mul_one]
    unfold family
    simp_rw [he]
    simp
  · have hex : ∃ j,j≠k ∧ u j≠v j := by
      by_contra hn
      apply hrest
      intro j hj
      by_contra huv
      exact hn ⟨j,hj,huv⟩
    obtain ⟨j,hj,hv⟩ := hex
    rw [if_neg hrest,mul_zero]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj,hv])

theorem tensorHamiltonian_eq_sum (A : Mat (Fin d)) (m : ℕ) :
    tensorHamiltonian A m=∑ k : Fin m,family (fun j => if j=k then A else (1 : Mat (Fin d))) := by
  ext u v
  simp only [tensorHamiltonian,Matrix.sum_apply,single_entry]

theorem tensorHamiltonian_in_basis (H : Mat (Fin d)) (U : Mat (Fin d)) (hU : IsUnitary U)
    (E : (Fin d) → ℝ) (hH : H=evolve U (diagonal (fun i => (E i : ℂ)))) (m : ℕ) :
    tensorHamiltonian H m=evolve (tensorMatrix U m)
      (diagonal (fun u : Fin m → (Fin d) => ((∑ k,E (u k) : ℝ) : ℂ))) := by
  let D := diagonal (fun i => (E i : ℂ))
  have hd (k : Fin m) : family (fun j => if j=k then D else (1 : Mat (Fin d))) =
      diagonal (fun u : Fin m → (Fin d) => (E (u k) : ℂ)) := by
    have he : (fun j => if j=k then D else (1 : Mat (Fin d))) =
        (fun j => diagonal (fun i => if j=k then (E i : ℂ) else 1)) := by
      funext j
      by_cases hj : j=k <;> simp [hj,D]
    rw [he,family_diagonal]
    congr 1
    funext u
    simp
  have he (k : Fin m) : evolve (tensorMatrix U m)
      (family (fun j => if j=k then D else (1 : Mat (Fin d)))) =
      family (fun j => if j=k then H else (1 : Mat (Fin d))) := by
    change evolve (family (fun _ : Fin m => U)) _ = _
    rw [family_evolve]
    congr 1
    funext j
    by_cases hj : j=k
    · simp only [hj,if_true]; exact hH.symm
    · simp only [hj,if_false,evolve,mul_one,hU.2]
  calc
    tensorHamiltonian H m = ∑ k : Fin m,family (fun j => if j=k then H else (1 : Mat (Fin d))) :=
      tensorHamiltonian_eq_sum H m
    _ = ∑ k : Fin m,evolve (tensorMatrix U m) (diagonal (fun u => (E (u k) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hd,he]
    _ = evolve (tensorMatrix U m) (diagonal (fun u : Fin m → (Fin d) => ((∑ k,E (u k) : ℝ) : ℂ))) := by
      have hs : (∑ k : Fin m,diagonal (fun u : Fin m → Fin d => (E (u k) : ℂ))) =
          diagonal (fun u => ((∑ k,E (u k) : ℝ) : ℂ)) := by
        ext u v
        by_cases huv : u=v
        · subst v; simp [Matrix.sum_apply,Complex.ofReal_sum]
        · simp [Matrix.sum_apply,Matrix.diagonal,huv]
      simp only [evolve,← Finset.sum_mul,← Finset.mul_sum,hs]

def hamiltonian (H : Hamiltonian (Fin d)) (m : ℕ) : Hamiltonian (Fin m → (Fin d)) :=
  ⟨tensorHamiltonian H.matrix m,by
    rw [tensorHamiltonian_in_basis H.matrix (H.hermitian.eigenvectorUnitary : Mat (Fin d))
      H.hermitian.eigenvectorUnitary.property H.hermitian.eigenvalues H.hermitian.spectral_theorem]
    exact Matrix.isHermitian_mul_mul_conjTranspose _
      (FlatMatrix.diagonalHamiltonian (Fin m → (Fin d))
        (fun u => ∑ k,H.hermitian.eigenvalues (u k))).hermitian⟩

theorem gibbs_tensor (β : ℝ) (H : Hamiltonian (Fin d)) (m : ℕ) :
    gibbs β (hamiltonian H m)=tensorMatrix (gibbs β H) m := by
  let U : Mat (Fin d) := H.hermitian.eigenvectorUnitary
  let E := H.hermitian.eigenvalues
  have hU : IsUnitary U := H.hermitian.eigenvectorUnitary.property
  have hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ))) := H.hermitian.spectral_theorem
  have hT := tensorHamiltonian_in_basis H.matrix U hU E hH m
  rw [FactoryGibbs.gibbs_in_basis β (hamiltonian H m) (tensorMatrix U m)
    (tensorMatrix_unitary U hU m) _ hT,FactoryGibbs.gibbs_in_basis β H U hU E hH,
    tensorMatrix_evolve,tensorMatrix_diagonal]
  have hexp (u : Fin m → (Fin d)) : Real.exp (-β*∑ k,E (u k))=∏ k,Real.exp (-β*E (u k)) := by
    rw [Finset.mul_sum,Real.exp_sum]
  have hz : (∑ u : Fin m → (Fin d),Real.exp (-β*∑ k,E (u k))) =
      ∏ _ : Fin m,(∑ j,Real.exp (-β*E j)) := by
    simp only [hexp]
    exact (Fintype.prod_sum (fun (_ : Fin m) j => Real.exp (-β*E j))).symm
  congr 1
  congr 1
  funext u
  rw [hexp,hz,← Finset.prod_div_distrib]
  simp only [Complex.ofReal_prod]

end ScheduleLaw.Blueprint.FactoryTensor
