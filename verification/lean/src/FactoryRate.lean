import FactoryEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryRate
open History

def decoded {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ) (n : ℕ) :
    Density (Fin (n+1) → Fin d) where
  matrix := partialRight (evolve (C.unitary n) (((C.rank n : ℂ)⁻¹) • C.projection n))
  positive := partialRight_positive ((FactoryCoding.flatDensity (C.projection n)
    (C.projection_hermitian n) (C.projection_idempotent n) (C.rank n) (C.rank_pos n)
    (C.projection_trace n)).positive.mul_mul_conjTranspose_same (C.unitary n))
  normalized := by
    rw [partialRight_trace,evolve_trace _ _ (C.unitary_isUnitary n),trace_smul,
      C.projection_trace,smul_eq_mul,inv_mul_cancel₀ (by exact_mod_cast (C.rank_pos n).ne')]

theorem energy_error {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ)
    (H : Hamiltonian (Fin d)) (n : ℕ) :
    |energy (tensorHamiltonian H.matrix (n+1)) (decoded C n).matrix/(n+1 : ℝ)-
      energy H.matrix τ.matrix| ≤ (2*(∑ i,|H.hermitian.eigenvalues i|))*C.error n := by
  let m : ℝ := n+1
  let M : ℝ := ∑ i,|H.hermitian.eigenvalues i|
  have hm : 0 < m := by dsimp [m]; positivity
  have hdist : traceDistance (decoded C n).matrix (tensorPower τ.matrix (n+1))≤C.error n :=
    C.approximation n
  have hdist0 : 0≤traceDistance (decoded C n).matrix (tensorPower τ.matrix (n+1)) :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by norm_num)
  have he := FactoryEnergy.energy_distance (tensorHamiltonian H.matrix (n+1))
    (decoded C n).matrix (tensorPower τ.matrix (n+1))
  rw [FactoryEnergy.tensor_energy] at he
  have hn : ‖tensorHamiltonian H.matrix (n+1)‖≤ m *M := by
    simpa only [Nat.cast_add,Nat.cast_one] using FactoryEnergy.tensor_norm_bound H (n+1)
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hb : |energy (tensorHamiltonian H.matrix (n+1)) (decoded C n).matrix-
      m *energy H.matrix τ.matrix|≤2*(m *M)*C.error n := by
    calc
      _ ≤ 2*‖tensorHamiltonian H.matrix (n+1)‖*
          traceDistance (decoded C n).matrix (tensorPower τ.matrix (n+1)) := he
      _ ≤ 2*(m *M)*traceDistance (decoded C n).matrix (tensorPower τ.matrix (n+1)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hdist0
      _ ≤ 2*(m *M)*C.error n := mul_le_mul_of_nonneg_left hdist (by dsimp [m,M]; positivity)
  have hid : energy (tensorHamiltonian H.matrix (n+1)) (decoded C n).matrix/m-
      energy H.matrix τ.matrix =
      (energy (tensorHamiltonian H.matrix (n+1)) (decoded C n).matrix-
        m *energy H.matrix τ.matrix)/m := by field_simp
  change |energy (tensorHamiltonian H.matrix (n+1)) (decoded C n).matrix/m-
    energy H.matrix τ.matrix|≤(2*M)*C.error n
  rw [hid,abs_div,abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  calc _ ≤ 2*(m *M)*C.error n := hb
       _ = (2*M)*C.error n*m := by ring

theorem energy_rate {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ)
    (H : Hamiltonian (Fin d)) :
    Tendsto (fun n => energy (tensorHamiltonian H.matrix (n+1)) (decoded C n).matrix/(n+1 : ℝ))
      atTop (𝓝 (energy H.matrix τ.matrix)) := by
  have ht : Tendsto (fun n => (2*(∑ i,|H.hermitian.eigenvalues i|))*C.error n) atTop (𝓝 0) := by
    simpa only [mul_zero] using C.error_vanishes.const_mul (2*(∑ i,|H.hermitian.eigenvalues i|))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero (fun n => abs_nonneg _) (fun n => energy_error C H n) ht

theorem relative_free_identity {d : ℕ} (β : ℝ) (τ q : Density (Fin d)) :
    faithfulRelativeEntropy τ.matrix q.matrix/β =
      energy (tangentHamiltonian β q) τ.matrix-entropy τ.matrix/β := by
  rw [tangentHamiltonian,energy_observable_weight]
  unfold faithfulRelativeEntropy energy
  rw [trace_mul_comm (matrixLog q.matrix) τ.matrix]
  ring

/-- The actual decoded code energy, integer rank and literal retained residue
 give the factory debit rate. No real proxy is substituted for the rank. -/
theorem debit_rate {d : ℕ} (β : ℝ) (τ q : Density (Fin d)) (C : SmallResidueCoding τ) :
    Tendsto (fun n => energy (tensorHamiltonian (tangentHamiltonian β q) (n+1))
        (decoded C n).matrix/(n+1 : ℝ)+
      (Real.log (C.residue n : ℝ)/(n+1 : ℝ)-Real.log (C.rank n : ℝ)/(n+1 : ℝ))/β+
      2/(n+1 : ℝ)) atTop (𝓝 (faithfulRelativeEntropy τ.matrix q.matrix/β)) := by
  have he := energy_rate C (FactoryGibbs.tangent β q)
  have hr := (C.residue_rate.sub C.rank_rate).div_const β
  have ht : Tendsto (fun n : ℕ => 2/(n+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2
  rw [relative_free_identity]
  simpa only [FactoryGibbs.tangent,sub_zero,zero_sub,zero_add,add_zero,neg_div,sub_eq_add_neg] using
    (he.add hr).add ht

end ScheduleLaw.Blueprint.FactoryRate
