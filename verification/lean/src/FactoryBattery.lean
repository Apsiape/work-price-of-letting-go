import FactoryGibbs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw.Blueprint.FactoryBattery
open History

variable {a : Type} [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
theorem diagonal_nonneg (ρ : Density a) (j : a) : 0≤(ρ.matrix j j).re :=
  (Complex.nonneg_iff.mp ρ.positive.diag_nonneg).1

omit [DecidableEq a] in
theorem diagonal_sum (ρ : Density a) : ∑ j,(ρ.matrix j j).re=1 := by
  simpa only [Matrix.trace,Matrix.diag_apply,Complex.re_sum,Complex.one_re] using
    congrArg Complex.re ρ.normalized

theorem absolute_tail (ρ : Density a) (E : a → ℝ) (nom : a) (A : ℝ)
    (hgap : ∀ j,|E j-E nom|≤A) :
    (∑ j,|E j-E nom| *(ρ.matrix j j).re) ≤ A*(1-(ρ.matrix nom nom).re) := by
  have hi (j : a) : |E j-E nom| *(ρ.matrix j j).re ≤
      A*(ρ.matrix j j).re-(if j=nom then A*(ρ.matrix j j).re else 0) := by
    by_cases hj : j=nom
    · subst j; simp
    · simp only [hj,if_false,sub_zero]
      exact mul_le_mul_of_nonneg_right (hgap j) (diagonal_nonneg ρ j)
  calc
    _ ≤ ∑ j,(A*(ρ.matrix j j).re-(if j=nom then A*(ρ.matrix j j).re else 0)) :=
      Finset.sum_le_sum (fun j _ => hi j)
    _ = A*(1-(ρ.matrix nom nom).re) := by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,diagonal_sum]
      simp
      ring

theorem entropy_bound (ρ : Density a) (nom : a) (M : ℝ) :
    entropy ρ.matrix ≤ M*(1-(ρ.matrix nom nom).re)+(Fintype.card a : ℝ)*Real.exp (-M) := by
  letI : Nonempty a := ⟨nom⟩
  let H := FlatMatrix.diagonalHamiltonian a (fun j => if j=nom then 0 else M)
  let γ : Density a := ⟨gibbs 1 H,gibbs_positive 1 H,gibbs_trace 1 H⟩
  have hrel := relative_entropy_nonnegative ρ γ (gibbs_faithful 1 H)
  change 0≤faithfulRelativeEntropy ρ.matrix (gibbs 1 H) at hrel
  rw [gibbs_relative_identity 1 H ρ.matrix ρ.normalized,one_mul] at hrel
  have he : energy H.matrix ρ.matrix=M*(1-(ρ.matrix nom nom).re) := by
    have he0 : energy H.matrix ρ.matrix=∑ j,(if j=nom then 0 else M)*(ρ.matrix j j).re := by
      simp only [energy,H,FlatMatrix.diagonalHamiltonian,diagonal_mul,Matrix.trace,
        Matrix.diag_apply,Complex.re_sum,Complex.re_ofReal_mul]
    rw [he0]
    have hi (j : a) : (if j=nom then 0 else M)*(ρ.matrix j j).re =
        M*(ρ.matrix j j).re-(if j=nom then M*(ρ.matrix j j).re else 0) := by
      split_ifs <;> ring
    simp_rw [hi]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,diagonal_sum]
    simp
    ring
  have hz : partition 1 H ≤ 1+(Fintype.card a : ℝ)*Real.exp (-M) := by
    rw [FlatMatrix.diagonal_partition]
    calc
      _ ≤ ∑ j : a,((if j=nom then 1 else 0)+Real.exp (-M)) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j=nom <;> simp [hj,le_of_lt (Real.exp_pos (-M))]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hl : Real.log (partition 1 H)≤(Fintype.card a : ℝ)*Real.exp (-M) := by
    have h := Real.log_le_sub_one_of_pos (partition_positive 1 H)
    linarith
  rw [he] at hrel
  linarith

/-- Fixed finite battery dimension: any requested entropy budget follows by
 making the actual nominal failure probability small. No diagonal-state
 hypothesis is used. -/
theorem entropy_tolerance (nom : a) (η : ℝ) (hη : 0<η) :
    ∃ ε : ℝ,0<ε ∧ ∀ ρ : Density a,
      1-(ρ.matrix nom nom).re≤ε → entropy ρ.matrix≤η := by
  have ht : Tendsto (fun M : ℝ => (Fintype.card a : ℝ)*Real.exp (-M)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa only [mul_zero] using (tendsto_const_nhds.mul he)
  have hev : ∀ᶠ M : ℝ in atTop,(Fintype.card a : ℝ)*Real.exp (-M)<η/2 :=
    (tendsto_order.mp ht).2 (η/2) (by positivity)
  obtain ⟨M,hM,hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and hev).exists
  refine ⟨η/(2*M),by positivity,fun ρ hρ => ?_⟩
  have hb := entropy_bound ρ nom M
  have hmul := mul_le_mul_of_nonneg_left hρ hM.le
  have heq : M*(η/(2*M))=η/2 := by field_simp
  rw [heq] at hmul
  linarith

end ScheduleLaw.Blueprint.FactoryBattery
