import BlueprintContracts

/-! Mixture-state entropy accounting and the two semicontinuity consequences.
Uses the already pinned QuantumInfo relative-entropy proofs, without a new
analytic premise or an entropy differentiation theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder Topology InnerProductSpace RealInnerProductSpace Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint

def mixWeight (n : ℕ) : ℝ := 1/((n : ℝ)+2)

theorem mixWeight_pos (n : ℕ) : 0 < mixWeight n := by unfold mixWeight; positivity

theorem mixWeight_lt_one (n : ℕ) : mixWeight n < 1 := by
  unfold mixWeight
  apply (div_lt_one (by positivity : (0 : ℝ) < n+2)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

def mixSequence {d : ℕ} (ρ ζ : MState (Fin d)) (n : ℕ) : MState (Fin d) where
  M := (1-mixWeight n) • ζ.M + mixWeight n • ρ.M
  nonneg := add_nonneg (smul_nonneg (sub_nonneg.mpr (mixWeight_lt_one n).le) ζ.nonneg)
    (smul_nonneg (mixWeight_pos n).le ρ.nonneg)
  tr := by simp [HermitianMat.trace_add,HermitianMat.trace_smul]

theorem mixSequence_tendsto {d : ℕ} (ρ ζ : MState (Fin d)) :
    Tendsto (mixSequence ρ ζ) atTop (𝓝 ζ) := by
  have ht : Tendsto mixWeight atTop (𝓝 (0 : ℝ)) := by
    have hb : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hn : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [hb.eventually (eventually_ge_atTop b)] with n hn
      linarith
    change Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 (0 : ℝ))
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  apply MState.toMat_IsEmbedding.tendsto_nhds_iff.mpr
  change Tendsto (fun n => (1-mixWeight n) • ζ.M+mixWeight n • ρ.M) atTop (𝓝 ζ.M)
  have hc : Tendsto (fun n => 1-mixWeight n) atTop (𝓝 (1 : ℝ)) := by
    simpa using (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub ht
  simpa using (hc.smul_const ζ.M).add (ht.smul_const ρ.M)

theorem mixSequence_kernel {d : ℕ} (ρ ζ : MState (Fin d)) (n : ℕ) :
    (mixSequence ρ ζ n).M.ker = ζ.M.ker ⊓ ρ.M.ker := by
  change ((1-mixWeight n) • ζ.M+mixWeight n • ρ.M).ker = _
  rw [HermitianMat.ker_add (smul_nonneg (by linarith [mixWeight_lt_one n]) ζ.nonneg)
    (smul_nonneg (mixWeight_pos n).le ρ.nonneg),
    HermitianMat.ker_pos_smul _ (ne_of_gt (by linarith [mixWeight_lt_one n])),
    HermitianMat.ker_pos_smul _ (ne_of_gt (mixWeight_pos n))]

theorem library_entropy_inner {d : ℕ} (ρ : MState (Fin d)) :
    Sᵥₙ ρ = -⟪ρ.M,ρ.M.log⟫_ℝ := by
  rw [Sᵥₙ_eq_neg_trace_log,real_inner_comm]

/-- Maximality along a sequence of strict mixtures forces a lower bound
on cross-log expectation. Only relative-entropy positivity is needed. -/
theorem mix_max_log_lower {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (ρ ζ : MState (Fin d)) (er ez : ℝ)
    (hmax : ∀ n, Sᵥₙ (mixSequence ρ ζ n)/β+
      (1-mixWeight n)*ez+mixWeight n*er ≤ Sᵥₙ ζ/β+ez) (n : ℕ) :
    β*(er-ez)-Sᵥₙ ζ ≤ ⟪ρ.M,(mixSequence ρ ζ n).M.log⟫_ℝ := by
  have hk : (mixSequence ρ ζ n).M.ker ≤ ζ.M.ker := by
    rw [mixSequence_kernel]; exact inf_le_left
  have hp := inner_log_sub_log_nonneg (ρ := ζ) (σ := mixSequence ρ ζ n) hk
  rw [inner_sub_right,← neg_eq_iff_eq_neg.mpr (library_entropy_inner ζ)] at hp
  have he := library_entropy_inner (mixSequence ρ ζ n)
  change Sᵥₙ (mixSequence ρ ζ n) = -⟪(1-mixWeight n) • ζ.M+mixWeight n • ρ.M,
    (mixSequence ρ ζ n).M.log⟫_ℝ at he
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left] at he
  have hm := mul_le_mul_of_nonneg_right (hmax n) hβ.le
  simp only [add_mul,div_mul_cancel₀ _ hβ.ne'] at hm
  have hprod : mixWeight n * (β*(er-ez)-Sᵥₙ ζ-
      ⟪ρ.M,(mixSequence ρ ζ n).M.log⟫_ℝ) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hp (by linarith [mixWeight_lt_one n] : 0 ≤ 1-mixWeight n)]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hprod (mixWeight_pos n))

/-- The support conclusion follows from the singular endpoint of the
already proved relative-entropy lower semicontinuity theorem. -/
theorem mix_max_kernel {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (ρ ζ : MState (Fin d)) (er ez : ℝ)
    (hmax : ∀ n, Sᵥₙ (mixSequence ρ ζ n)/β+
      (1-mixWeight n)*ez+mixWeight n*er ≤ Sᵥₙ ζ/β+ez) : ζ.M.ker ≤ ρ.M.ker := by
  by_contra hnot
  obtain ⟨N,hN⟩ := exists_nat_gt (-Sᵥₙ ρ-(β*(er-ez)-Sᵥₙ ζ))
  have hev := (mixSequence_tendsto ρ ζ).eventually
    (qRelativeEnt_lowerSemicontinuous_2 ρ ζ hnot (N : ENNReal) (by simp))
  obtain ⟨n,hn⟩ := hev.exists
  have hk : (mixSequence ρ ζ n).M.ker ≤ ρ.M.ker := by
    rw [mixSequence_kernel]; exact inf_le_right
  rw [if_pos hk] at hn
  have hcast : ((N : ENNReal) : EReal)=((N : ℝ) : EReal) := by
    calc ((N : ENNReal) : EReal) = (((N : ENNReal).toReal : ℝ) : EReal) :=
        (EReal.coe_ennreal_toReal (by simp)).symm
      _ = _ := by simp
  rw [hcast] at hn
  have hn' : (N : ℝ) < ⟪ρ.M,ρ.M.log-(mixSequence ρ ζ n).M.log⟫_ℝ := by
    exact_mod_cast hn
  rw [inner_sub_right] at hn'
  have he := library_entropy_inner ρ
  have hb := mix_max_log_lower β hβ ρ ζ er ez hmax n
  linarith

/-- Upper semicontinuity of the log expectation yields the directional
inequality directly; differentiating the matrix entropy is unnecessary. -/
theorem mix_max_tangent {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (ρ ζ : MState (Fin d)) (er ez : ℝ) (hk : ζ.M.ker ≤ ρ.M.ker)
    (hmax : ∀ n, Sᵥₙ (mixSequence ρ ζ n)/β+
      (1-mixWeight n)*ez+mixWeight n*er ≤ Sᵥₙ ζ/β+ez) :
    er-⟪ρ.M,ζ.M.log⟫_ℝ/β ≤ Sᵥₙ ζ/β+ez := by
  have hcross : β*(er-ez)-Sᵥₙ ζ ≤ ⟪ρ.M,ζ.M.log⟫_ℝ := by
    by_contra h
    have he := (mixSequence_tendsto ρ ζ).eventually
      (inner_log_bounded_near hk (lt_of_not_ge h))
    obtain ⟨n,hn⟩ := he.exists
    have hnk : (mixSequence ρ ζ n).M.ker ≤ ρ.M.ker := by
      rw [mixSequence_kernel]; exact inf_le_right
    exact (not_lt_of_ge (mix_max_log_lower β hβ ρ ζ er ez hmax n)) (hn hnk)
  apply (mul_le_mul_iff_of_pos_right hβ).mp
  simp only [sub_mul,add_mul,div_mul_cancel₀ _ hβ.ne']
  nlinarith

theorem kernelContained_library_iff {d : ℕ} (ρ ζ : Density (Fin d)) :
    KernelContained ρ.matrix ζ.matrix ↔ ζ.toMState.M.ker ≤ ρ.toMState.M.ker := by
  constructor
  · intro h v hv
    rw [HermitianMat.mem_ker_iff_mulVec_zero] at hv ⊢
    exact h v hv
  · intro h v hv
    have h0 : WithLp.toLp 2 v ∈ ζ.toMState.M.ker := by
      rw [HermitianMat.mem_ker_iff_mulVec_zero]
      exact hv
    have h1 := h h0
    rw [HermitianMat.mem_ker_iff_mulVec_zero] at h1
    exact h1

theorem mstate_entropy_eq {d : ℕ} (ρ : MState (Fin d)) : Sᵥₙ ρ = entropy ρ.m := by
  let D : Density (Fin d) := ⟨ρ.m,ρ.psd,ρ.tr'⟩
  have hD : D.toMState=ρ := MState.ext_m rfl
  rw [← hD,← density_entropy_eq_library]
  rfl

theorem convex_section_mix_max {d : ℕ} (β : ℝ)
    (K : Set (Mat (Fin d) × ℝ)) (hconv : Convex ℝ K)
    (ρ ζ : Density (Fin d)) (er ez : ℝ)
    (hr : (ρ.matrix,er) ∈ K) (hz : (ζ.matrix,ez) ∈ K)
    (hmax : ∀ x ∈ K, entropy x.1/β+x.2 ≤ entropy ζ.matrix/β+ez) :
    ∀ n, Sᵥₙ (mixSequence ρ.toMState ζ.toMState n)/β+
      (1-mixWeight n)*ez+mixWeight n*er ≤ Sᵥₙ ζ.toMState/β+ez := by
  intro n
  have hc := hconv hz hr (sub_nonneg.mpr (mixWeight_lt_one n).le)
    (mixWeight_pos n).le (by ring : (1-mixWeight n)+mixWeight n=1)
  have h := hmax _ hc
  rw [mstate_entropy_eq,mstate_entropy_eq]
  change entropy ((1-mixWeight n) • ζ.matrix+mixWeight n • ρ.matrix)/β+
    (1-mixWeight n)*ez+mixWeight n*er ≤ entropy ζ.matrix/β+ez
  change entropy ((1-mixWeight n) • ζ.matrix+mixWeight n • ρ.matrix)/β+
    ((1-mixWeight n)*ez+mixWeight n*er) ≤ entropy ζ.matrix/β+ez at h
  simpa only [add_assoc] using h

theorem cross_log_energy {d : ℕ} (ρ ζ : Density (Fin d)) :
    ⟪ρ.toMState.M,ζ.toMState.M.log⟫_ℝ = energy (matrixLog ζ.matrix) ρ.matrix := by
  rw [HermitianMat.inner_eq_re_trace,library_log_matrix]
  exact congrArg Complex.re (trace_mul_comm _ _)

#print axioms mixWeight
#print axioms mixWeight_pos
#print axioms mixWeight_lt_one
#print axioms mixSequence
#print axioms mixSequence_tendsto
#print axioms mixSequence_kernel
#print axioms library_entropy_inner
#print axioms mix_max_log_lower
#print axioms mix_max_kernel
#print axioms mix_max_tangent
#print axioms kernelContained_library_iff
#print axioms mstate_entropy_eq
#print axioms cross_log_energy
#print axioms convex_section_mix_max
end ScheduleLaw.Blueprint
