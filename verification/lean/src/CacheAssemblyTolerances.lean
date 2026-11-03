import CacheRefundBounds

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter
open scoped Topology
namespace ScheduleLaw.Blueprint.CacheAssemblyTolerances

theorem entropy_cutoff (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ 64*Real.exp (-M) ≤ η/2 := by
  let M := max 1 (Real.log (128/η))
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have he : Real.exp (-M) ≤ Real.exp (-Real.log (128/η)) :=
    Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
  have hex : Real.exp (-Real.log (128/η)) = (128/η)⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hη)]
  rw [hex] at he
  refine ⟨M,hM,?_⟩
  calc 64*Real.exp (-M) ≤ 64*(128/η)⁻¹ := mul_le_mul_of_nonneg_left he (by norm_num)
       _ = η/2 := by
         rw [inv_div]
         ring

theorem factory_failure (A η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ f : ℝ, 0 < f ∧ A*f ≤ η/3 := by
  refine ⟨η/(3*(A+1)),by positivity,?_⟩
  apply (le_div_iff₀ (by norm_num : (0 : ℝ)<3)).mpr
  have he : (η/(3*(A+1)))*(3*(A+1))=η := div_mul_cancel₀ _ (by positivity)
  nlinarith [div_nonneg hη.le (by positivity : (0 : ℝ) ≤ 3*(A+1))]

theorem eventually_all (d : ℕ) (a err : ℕ → ℝ) (rate A L Λ M η : ℝ)
    (hη : 0 < η) (ha : Tendsto a atTop (𝓝 rate)) (herr : Vanishes err) :
    ∀ᶠ m : ℕ in atTop,
      0 < m ∧ 2/(m : ℝ) ≤ η ∧ M/(m : ℝ) ≤ η/2 ∧
      2*L/(m : ℝ) ≤ η/3 ∧ A*err m ≤ η/3 ∧
      CacheRefundBounds.modulus d (err m) ≤ η ∧
      2*(|a m|+Λ)*err m ≤ η ∧ a m ≤ rate+η := by
  have hi : Tendsto (fun m : ℕ => 1/(m : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun m : ℕ => 2/(m : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using hi.const_mul 2
  have hM : Tendsto (fun m : ℕ => M/(m : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using hi.const_mul M
  have hL : Tendsto (fun m : ℕ => 2*L/(m : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using hi.const_mul (2*L)
  have hA : Tendsto (fun m => A*err m) atTop (𝓝 0) := by
    simpa only [mul_zero] using herr.const_mul A
  have hS := CacheRefundBounds.modulus_vanishes d err herr
  have hE : Tendsto (fun m => 2*(|a m|+Λ)*err m) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((ha.abs.add_const Λ).const_mul 2).mul herr
  filter_upwards [eventually_gt_atTop 0,
    h2.eventually (gt_mem_nhds hη),
    hM.eventually (gt_mem_nhds (show 0<η/2 by positivity)),
    hL.eventually (gt_mem_nhds (show 0<η/3 by positivity)),
    hA.eventually (gt_mem_nhds (show 0<η/3 by positivity)),
    hS.eventually (gt_mem_nhds hη),hE.eventually (gt_mem_nhds hη),
    ha.eventually (gt_mem_nhds (show rate<rate+η by linarith))] with m hm h2 hM hL hA hS hE ha
  exact ⟨hm,h2.le,hM.le,hL.le,hA.le,hS.le,hE.le,ha.le⟩

end ScheduleLaw.Blueprint.CacheAssemblyTolerances
