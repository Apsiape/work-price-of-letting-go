import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

/-!
# Partial reset costs as much as full reset in real time (Section 4.2)

With `h(y) = -y log y - (1-y) log(1-y)` (nats) and `c = βΔ`, the real-time rate of amplitude
damping is `max_{0 ≤ y ≤ p} [h(y) - c y]` (in nats; divide by `ln 2` for bits).  We prove:

* `gibbs_bound`: `h(y) - c y ≤ log(1 + e^{-c})` for every `y ∈ [0, 1]`;
* `value_at_opt`: equality at `y* = 1/(1 + e^{c})`;
* `saturation`: hence, once `p ≥ 1/(1 + e^{βΔ})`, the maximum over `[0, p]` is the full-reset
  cost `log(1 + e^{-βΔ})`.
-/

namespace FullReset

open Real

/-- Binary entropy in nats. -/
noncomputable def h (y : ℝ) : ℝ := -y * log y - (1 - y) * log (1 - y)

/-- `y log y - y log q ≥ y - q` for `y ≥ 0`, `q > 0` (from `log x ≤ x - 1`). -/
theorem xlog_ge {y q : ℝ} (hy : 0 ≤ y) (hq : 0 < q) : y - q ≤ y * log y - y * log q := by
  rcases hy.lt_or_eq with hy | hy
  · have hl := Real.log_le_sub_one_of_pos (div_pos hq hy)
    rw [Real.log_div hq.ne' hy.ne'] at hl
    have h2 : y * (log q - log y) ≤ y * (q / y - 1) := mul_le_mul_of_nonneg_left hl hy.le
    have e : y * (q / y - 1) = q - y := by field_simp
    linarith
  · subst hy
    simp
    linarith

theorem gibbs_bound (c : ℝ) {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    h y - c * y ≤ log (1 + exp (-c)) := by
  set L := log (1 + exp (-c))
  have hE : 0 < exp (-c) := exp_pos _
  have hZ : 0 < 1 + exp (-c) := by linarith
  have h1q' : 1 - exp (-c) / (1 + exp (-c)) = 1 / (1 + exp (-c)) := by
    rw [eq_div_iff hZ.ne', sub_mul, div_mul_cancel₀ _ hZ.ne']
    ring
  set q := exp (-c) / (1 + exp (-c))
  have hq : 0 < q := div_pos hE hZ
  have h1q : 1 - q = 1 / (1 + exp (-c)) := h1q'
  have hq1 : 0 < 1 - q := by rw [h1q]; positivity
  have hlq : log q = -c - L := by
    rw [Real.log_div hE.ne' hZ.ne', Real.log_exp]
  have hl1q : log (1 - q) = -L := by
    rw [h1q, Real.log_div one_ne_zero hZ.ne', Real.log_one]
    ring
  have a1 := xlog_ge h0 hq
  have a2 := xlog_ge (by linarith : 0 ≤ 1 - y) hq1
  rw [hlq] at a1
  rw [hl1q] at a2
  unfold h
  nlinarith

theorem value_at_opt (c : ℝ) :
    h (1 / (1 + exp c)) - c * (1 / (1 + exp c)) = log (1 + exp (-c)) := by
  set L := log (1 + exp (-c))
  have hE : 0 < exp (-c) := exp_pos _
  have hZ : 0 < 1 + exp (-c) := by linarith
  have hy : 1 / (1 + exp c) = exp (-c) / (1 + exp (-c)) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hy]
  have h1q' : 1 - exp (-c) / (1 + exp (-c)) = 1 / (1 + exp (-c)) := by
    rw [eq_div_iff hZ.ne', sub_mul, div_mul_cancel₀ _ hZ.ne']
    ring
  set q := exp (-c) / (1 + exp (-c))
  have h1q : 1 - q = 1 / (1 + exp (-c)) := h1q'
  have hlq : log q = -c - L := by
    rw [Real.log_div hE.ne' hZ.ne', Real.log_exp]
  have hl1q : log (1 - q) = -L := by
    rw [h1q, Real.log_div one_ne_zero hZ.ne', Real.log_one]
    ring
  unfold h
  rw [hlq, hl1q]
  ring

/-- Once `p ≥ 1/(1 + e^{c})`, the maximum of `h(y) - c y` over `[0, p]` is `log(1 + e^{-c})`. -/
theorem saturation (c : ℝ) {p : ℝ} (hp : 1 / (1 + exp c) ≤ p) (hp1 : p ≤ 1) :
    IsGreatest ((fun y => h y - c * y) '' Set.Icc 0 p) (log (1 + exp (-c))) := by
  refine ⟨⟨1 / (1 + exp c), ⟨by positivity, hp⟩, value_at_opt c⟩, ?_⟩
  rintro _ ⟨y, ⟨hy0, hyp⟩, rfl⟩
  exact gibbs_bound c hy0 (hyp.trans hp1)

end FullReset

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms FullReset.xlog_ge
#print axioms FullReset.gibbs_bound
#print axioms FullReset.value_at_opt
#print axioms FullReset.saturation
