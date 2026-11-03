import Proofs
import CircuitStates

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw

theorem trace_unitary_conjugation {a : Type} [Fintype a] [DecidableEq a]
    (U : unitary (Mat a)) (A : Mat a) :
    (Unitary.conjStarAlgAut ℂ (Mat a) U A).trace = A.trace := by
  simp only [Unitary.conjStarAlgAut_apply]
  rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

theorem entropy_trace_log {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Mat a) (hρ : ρ.IsHermitian) :
    entropy ρ = -(ρ * matrixLog ρ).trace.re := by
  let U := hρ.eigenvectorUnitary
  let D : Mat a := diagonal (fun i => (hρ.eigenvalues i : ℂ))
  let L : Mat a := diagonal (fun i => (Real.log (hρ.eigenvalues i) : ℂ))
  have hr : ρ = Unitary.conjStarAlgAut ℂ (Mat a) U D := hρ.spectral_theorem
  have hl : matrixLog ρ = Unitary.conjStarAlgAut ℂ (Mat a) U L := by
    simp only [matrixLog, dif_pos hρ, Matrix.IsHermitian.cfc]
    rfl
  have hp : ρ * matrixLog ρ = Unitary.conjStarAlgAut ℂ (Mat a) U (D * L) := by
    rw [map_mul]
    exact congrArg₂ (fun A B : Mat a => A * B) hr hl
  rw [hp, trace_unitary_conjugation, entropy_of_hermitian ρ hρ]
  simp [D,L,diagonal_mul_diagonal,trace_diagonal,Real.negMulLog,
    Complex.re_sum,Finset.sum_neg_distrib]

def partition {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (H : Hamiltonian a) : ℝ :=
  ∑ i, Real.exp (-β * H.hermitian.eigenvalues i)

theorem partition_positive {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) : 0 < partition β H :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem gibbs_positive {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) : (gibbs β H).PosSemidef := by
  unfold gibbs Matrix.IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  apply PosSemidef.mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  intro i
  apply Complex.nonneg_iff.mpr
  exact ⟨(div_pos (Real.exp_pos _) (partition_positive β H)).le,rfl⟩

theorem gibbs_faithful {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) : (gibbs β H).PosDef := by
  unfold gibbs Matrix.IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  apply PosDef.mul_mul_conjTranspose_same
  · rw [posDef_diagonal_iff]
    intro i
    apply Complex.pos_iff.mpr
    exact ⟨div_pos (Real.exp_pos _) (partition_positive β H),rfl⟩
  · exact Matrix.vecMul_injective_of_isUnit Unitary.isUnit_coe
theorem gibbs_trace {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) : (gibbs β H).trace = 1 := by
  unfold gibbs Matrix.IsHermitian.cfc
  rw [trace_unitary_conjugation,trace_diagonal]
  have hsum : ∑ i, Real.exp (-β * H.hermitian.eigenvalues i) / partition β H = 1 := by
    rw [← Finset.sum_div]
    exact div_self (partition_positive β H).ne'
  change ∑ i, ((Real.exp (-β * H.hermitian.eigenvalues i) / partition β H : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_sum,hsum,Complex.ofReal_one]

theorem gibbs_log {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) :
    matrixLog (gibbs β H) = (-β : ℂ) • H.matrix -
      (Real.log (partition β H) : ℂ) • (1 : Mat a) := by
  let f : ℝ → ℝ := fun x => Real.exp (-β*x) / partition β H
  have hγ := (gibbs_positive β H).isHermitian
  have he : gibbs β H = cfc f H.matrix := by
    rw [H.hermitian.cfc_eq]
    rfl
  have hlog : matrixLog (gibbs β H) = cfc Real.log (cfc f H.matrix) := by
    rw [matrixLog,dif_pos hγ,← hγ.cfc_eq,he]
  have hf : ContinuousOn f (spectrum ℝ H.matrix) := H.matrix.finite_real_spectrum.continuousOn f
  have hlf : ContinuousOn Real.log (f '' spectrum ℝ H.matrix) :=
    (H.matrix.finite_real_spectrum.image f).continuousOn Real.log
  have hcomp : cfc Real.log (cfc f H.matrix) = cfc (Real.log ∘ f) H.matrix :=
    (cfc_comp (R := ℝ) (p := IsSelfAdjoint) Real.log f H.matrix
      (show IsSelfAdjoint H.matrix from H.hermitian) hlf hf).symm
  rw [hlog,hcomp]
  have hx : Real.log ∘ f = fun x => -β*x - Real.log (partition β H) := by
    ext x
    simp [f,Real.log_div (Real.exp_pos _).ne' (partition_positive β H).ne',Real.log_exp]
  rw [hx]
  rw [cfc_sub ..,cfc_const_mul ..]
  have hi : cfc (fun x : ℝ => x) H.matrix = H.matrix :=
    cfc_id (R := ℝ) (p := IsSelfAdjoint) H.matrix H.hermitian
  have hc : cfc (fun _ : ℝ => Real.log (partition β H)) H.matrix =
      algebraMap ℝ (Mat a) (Real.log (partition β H)) :=
    cfc_const (p := IsSelfAdjoint) (Real.log (partition β H)) H.matrix H.hermitian
  rw [hi,hc]
  simp [Algebra.smul_def,Matrix.algebraMap_eq_diagonal]
  rfl

theorem gibbs_relative_identity {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) (ρ : Mat a) (htr : ρ.trace = 1) :
    faithfulRelativeEntropy ρ (gibbs β H) =
      -entropy ρ + β * energy H.matrix ρ + Real.log (partition β H) := by
  rw [faithfulRelativeEntropy,gibbs_log]
  simp only [mul_sub,Matrix.mul_smul,mul_one,trace_sub,trace_smul,Complex.sub_re,htr,
    mul_one]
  rw [trace_mul_comm ρ H.matrix]
  simp [energy,Complex.mul_re]
  ring

theorem gibbs_heat_identity {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (H : Hamiltonian a) (ρ : Mat a) (htr : ρ.trace = 1) :
    entropy ρ - entropy (gibbs β H) =
      β * (energy H.matrix ρ - energy H.matrix (gibbs β H)) -
      faithfulRelativeEntropy ρ (gibbs β H) := by
  have hself : faithfulRelativeEntropy (gibbs β H) (gibbs β H) = 0 := by
    unfold faithfulRelativeEntropy
    rw [entropy_trace_log _ (gibbs_positive β H).isHermitian]
    ring
  have hs := gibbs_relative_identity β H (gibbs β H) (gibbs_trace β H)
  have hr := gibbs_relative_identity β H ρ htr
  rw [hself] at hs
  nlinarith

theorem reservoir_entropy_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) :
    (engineLedger e t).reservoirEntropy = β * (engineLedger e t).reservoirEnergy -
      (engineLedger e t).relativeEntropy := by
  letI : Nonempty (Fin e.r) := ⟨⟨0,e.r_pos⟩⟩
  exact gibbs_heat_identity β e.HR (reservoirFinal e t) (reservoirFinal_density e t).2

end ScheduleLaw
