import PhaseEntropyLimit

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
open Filter
open scoped Topology
namespace ScheduleLaw.Blueprint.PhaseToleranceChoice

theorem inverse_vanishes (K : ℝ) : Vanishes (fun L : ℕ => K/(L+1 : ℝ)) := by
  simpa only [mul_one_div,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul K

/-- A single finite phase length controls service, all fixed-observable
continuity errors, and both dimension-dependent entropy refunds. -/
theorem eventually_all (c w rank : ℕ) (K C ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ L : ℕ in atTop,0<L ∧ K/(L+1 : ℝ)≤ζ ∧ C*(K/(L+1 : ℝ))≤ζ ∧
      2*(K/(L+1 : ℝ))≤ζ ∧ 2*(K/(L+1 : ℝ))≤1/2 ∧
      PhaseEntropyLimit.modulus c rank K L≤ζ ∧ PhaseEntropyLimit.modulus w 0 K L≤ζ := by
  have hd := inverse_vanishes K
  have hC : Tendsto (fun L : ℕ => C*(K/(L+1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul C
  have h2 : Tendsto (fun L : ℕ => 2*(K/(L+1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul 2
  filter_upwards [eventually_gt_atTop 0,hd.eventually (gt_mem_nhds hζ),
    hC.eventually (gt_mem_nhds hζ),h2.eventually (gt_mem_nhds hζ),
    h2.eventually (gt_mem_nhds (show (0 : ℝ)<1/2 by norm_num)),
    (PhaseEntropyLimit.vanishes c rank K).eventually (gt_mem_nhds hζ),
    (PhaseEntropyLimit.vanishes w 0 K).eventually (gt_mem_nhds hζ)] with L hL hd hC h2 hsmall hc hw
  exact ⟨hL,hd.le,hC.le,h2.le,hsmall.le,hc.le,hw.le⟩

end ScheduleLaw.Blueprint.PhaseToleranceChoice
