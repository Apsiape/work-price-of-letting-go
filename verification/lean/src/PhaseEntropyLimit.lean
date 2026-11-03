import CacheRefundBounds

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Filter
open scoped Topology
namespace ScheduleLaw.Blueprint.PhaseEntropyLimit

theorem log_padding : Tendsto (fun L : ℕ => Real.log ((L : ℝ)+4)/((L : ℝ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun L : ℕ => (L : ℝ)+4) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    obtain ⟨N,hN⟩ := exists_nat_gt x
    filter_upwards [eventually_ge_atTop N] with L hL
    have hNL : (N : ℝ)≤L := by exact_mod_cast hL
    linarith
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) 1 (by norm_num)).comp hn
  convert h using 1
  funext L
  simp only [Function.comp_apply,pow_one,one_mul]
  congr 1
  ring

def modulus (c r : ℕ) (K : ℝ) (L : ℕ) : ℝ :=
  2*(K/(L+1 : ℝ))*(Real.log c+(r : ℝ)*Real.log ((L : ℝ)+4))+
    FiniteFannesScalar.correction (2*(K/(L+1 : ℝ)))

/-- The finite Fannes cost vanishes even though the controller phase
space grows as a fixed power of L+4. -/
theorem vanishes (c r : ℕ) (K : ℝ) : Vanishes (modulus c r K) := by
  have hd : Tendsto (fun L : ℕ => K/(L+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul K
  have h1 : Tendsto (fun L : ℕ => 2*(K/(L+1 : ℝ))*Real.log c) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hd.const_mul 2).mul_const (Real.log c)
  have h2 : Tendsto (fun L : ℕ => (2*K*r)*(Real.log ((L : ℝ)+4)/(L+1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using log_padding.const_mul (2*K*r)
  have hc := FiniteFannesScalar.correction_tendsto_zero.comp (show
      Tendsto (fun L : ℕ => 2*(K/(L+1 : ℝ))) atTop (𝓝 0) by
        simpa only [mul_zero] using hd.const_mul 2)
  have h := (h1.add h2).add hc
  simp only [add_zero] at h
  change Tendsto (modulus c r K) atTop (𝓝 (0 : ℝ))
  convert h using 1
  funext L
  dsimp only [modulus,Function.comp_apply]
  ring

end ScheduleLaw.Blueprint.PhaseEntropyLimit
