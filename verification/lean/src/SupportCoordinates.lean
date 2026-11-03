import SupportBasis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.SupportBasis
open History

theorem boltzmann_in_basis {d : ℕ} (β : ℝ) (H : Hamiltonian (Fin d))
    (U : Mat (Fin d)) (hU : IsUnitary U) (E : Fin d → ℝ)
    (hH : H.matrix = evolve U (diagonal (fun i => (E i : ℂ)))) :
    boltzmann β H = evolve U (diagonal (fun i => (Real.exp (-β*E i) : ℂ))) := by
  letI := matrixCStarStructure (Fin d)
  let φ := Unitary.conjStarAlgAut ℂ (Mat (Fin d)) (⟨U,hU⟩ : unitaryGroup (Fin d) ℂ)
  let D : Mat (Fin d) := diagonal (fun i => (E i : ℂ))
  have hφ : φ D = H.matrix := hH.symm
  have hcf : cfc (fun x : ℝ => Real.exp (-β*x)) D =
      diagonal (fun i => (Real.exp (-β*E i) : ℂ)) := by
    exact ((FlatMatrix.diagonalHamiltonian (Fin d) E).hermitian.cfc_eq _).trans
      (FlatMatrix.diagonal_cfc (Fin d) E _ (by fun_prop))
  have hm := StarAlgHomClass.map_cfc φ (fun x : ℝ => Real.exp (-β*x)) D
    (hφ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := (FlatMatrix.diagonalHamiltonian (Fin d) E).hermitian)
    (hφa := by rw [hφ]; exact H.hermitian)
  rw [hφ] at hm
  change H.hermitian.cfc (fun x => Real.exp (-β*x)) = _
  rw [← H.hermitian.cfc_eq,← hm,hcf]
  rfl

/-- Literal finite energy and projection coordinates, plus the original
 restricted partition function. No commutation between P and Q is required. -/
theorem support_coordinates {d : ℕ} (β : ℝ) (H : Hamiltonian (Fin d))
    (P : Mat (Fin d)) (hP : P.IsHermitian) (hPi : P*P=P)
    (hPH : P*H.matrix=H.matrix*P) :
    ∃ (U : Mat (Fin d)) (E : Fin d → ℝ) (T : Finset (Fin d)),
      IsUnitary U ∧ H.matrix=evolve U (diagonal (fun i => (E i : ℂ))) ∧
      P=evolve U (diagonal (fun i => if i ∈ T then 1 else 0)) ∧
      energy P (boltzmann β H)=∑ i ∈ T,Real.exp (-β*E i) := by
  classical
  obtain ⟨b,E,F,hHb,hPb⟩ := joint_basis H.matrix P H.hermitian hP hPH.symm
  let U := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis
  have hU : IsUnitary U := (basis_diagonal b H.matrix E hHb).1
  have hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ))) := (basis_diagonal b H.matrix E hHb).2
  have hPmat : P=evolve U (diagonal (fun i => (F i : ℂ))) := (basis_diagonal b P F hPb).2
  let D : Mat (Fin d) := diagonal (fun i => (F i : ℂ))
  let φ := Unitary.conjStarAlgAut ℂ (Mat (Fin d)) (⟨U,hU⟩ : unitaryGroup (Fin d) ℂ)
  have hφ : φ D=P := hPmat.symm
  have hD : D*D=D := by
    apply φ.injective
    have hφr : φ.toRingEquiv D=P := hφ
    simpa only [map_mul,hφr] using hPi
  have h01 (i : Fin d) : F i=0 ∨ F i=1 := by
    change (diagonal (fun j => (F j : ℂ)))*(diagonal (fun j => (F j : ℂ))) =
      diagonal (fun j => (F j : ℂ)) at hD
    rw [diagonal_mul_diagonal] at hD
    have he := congrArg (fun A : Mat (Fin d) => A i i) hD
    simp only [diagonal_apply_eq] at he
    have hr : F i*F i=F i := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_mul] using he
    rcases mul_eq_zero.mp (show F i*(F i-1)=0 by nlinarith only [hr]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  let T := Finset.univ.filter (fun i => F i=1)
  have hDmask : D=diagonal (fun i => if i ∈ T then 1 else 0) := by
    apply congrArg diagonal
    funext i
    rcases h01 i with h0 | h1
    · simp [T,h0]
    · simp [T,h1]
  refine ⟨U,E,T,hU,hH,?_,?_⟩
  · rw [← hDmask]
    exact hPmat
  · rw [boltzmann_in_basis β H U hU E hH]
    change ((P * φ (diagonal (fun i => (Real.exp (-β*E i) : ℂ)))).trace).re = _
    rw [← hφ,← map_mul]
    change ((U*(D*diagonal (fun i => (Real.exp (-β*E i) : ℂ)))*Uᴴ).trace).re = _
    rw [Matrix.trace_mul_cycle, hU.1,one_mul,hDmask,diagonal_mul_diagonal,trace_diagonal]
    simp only [Complex.re_sum]
    have ht (i : Fin d) : ((if i ∈ T then 1 else 0 : ℂ)*
        (Real.exp (-β*E i) : ℂ)).re = if i ∈ T then Real.exp (-β*E i) else 0 := by
      split_ifs <;> simp only [one_mul,zero_mul,Complex.ofReal_re,Complex.zero_re]
    simp_rw [ht]
    rw [← Finset.sum_filter]
    simp

end ScheduleLaw.Blueprint.SupportBasis
