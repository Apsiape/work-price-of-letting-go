import FactoryTensorHamiltonian
import FactoryCoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryEnergy
open History FactoryTensor FiniteResidue

theorem norm_evolve {a : Type} [Fintype a] [DecidableEq a]
    (U A : Mat a) (hU : IsUnitary U) : ‖evolve U A‖=‖A‖ := by
  letI := matrixCStarStructure a
  let u : unitary (Mat a) := ⟨U,hU⟩
  change ‖(u : Mat a)*A*((star u : unitary (Mat a)) : Mat a)‖=‖A‖
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

theorem energy_distance {a : Type} [Fintype a] [DecidableEq a]
    (H A B : Mat a) : |energy H A-energy H B|≤2*‖H‖*traceDistance A B := by
  have he : energy H A-energy H B=energy H (A-B) := by
    simp only [energy,mul_sub,trace_sub,Complex.sub_re]
  rw [he]
  calc
    _ ≤ Matrix.traceNorm (H*(A-B)) :=
      (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
    _ ≤ ‖H‖*Matrix.traceNorm (A-B) := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = _ := by
      unfold traceDistance
      rw [ClassicalFlag.traceNorm_eq_library]
      ring

theorem tensor_norm_bound {d : ℕ} (H : Hamiltonian (Fin d)) (m : ℕ) :
    ‖tensorHamiltonian H.matrix m‖≤(m : ℝ)*(∑ i,|H.hermitian.eigenvalues i|) := by
  let U : Mat (Fin d) := H.hermitian.eigenvectorUnitary
  let E := H.hermitian.eigenvalues
  let M : ℝ := ∑ i,|E i|
  have hU : IsUnitary U := H.hermitian.eigenvectorUnitary.property
  rw [tensorHamiltonian_in_basis H.matrix U hU E H.hermitian.spectral_theorem m,
    norm_evolve _ _ (tensorMatrix_unitary U hU m),Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(m : ℝ)*M)).mpr
  intro u
  simp only [Complex.norm_real,Real.norm_eq_abs]
  calc
    |∑ k,E (u k)| ≤ ∑ k,|E (u k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin m,M := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.single_le_sum (fun i _ => abs_nonneg (E i)) (Finset.mem_univ (u k))
    _ = (m : ℝ)*M := by simp

theorem family_trace {d m : ℕ} (A : Fin m → Mat (Fin d)) :
    (family A).trace=∏ k,(A k).trace := by
  change (∑ u : Fin m → Fin d,∏ k,A k (u k) (u k))=∏ k,∑ i,A k i i
  exact (Fintype.prod_sum (fun k i => A k i i)).symm

theorem tensor_energy {d : ℕ} (H : Mat (Fin d)) (ρ : Density (Fin d)) (m : ℕ) :
    energy (tensorHamiltonian H m) (tensorPower ρ.matrix m)=(m : ℝ)*energy H ρ.matrix := by
  rw [tensorHamiltonian_eq_sum,ScheduleLaw.energy_sum]
  have hk (k : Fin m) : energy (family (fun j => if j=k then H else (1 : Mat (Fin d))))
      (tensorPower ρ.matrix m)=energy H ρ.matrix := by
    change ((family (fun j => if j=k then H else (1 : Mat (Fin d))))*
      family (fun _ : Fin m => ρ.matrix)).trace.re=energy H ρ.matrix
    rw [← family_mul,family_trace]
    have he (j : Fin m) : ((if j=k then H else (1 : Mat (Fin d)))*ρ.matrix).trace =
        if j=k then (H*ρ.matrix).trace else 1 := by
      by_cases hj : j=k <;> simp [hj,ρ.normalized]
    simp_rw [he]
    simp [energy]
  simp only [hk,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end ScheduleLaw.Blueprint.FactoryEnergy
