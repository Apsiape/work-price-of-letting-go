import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Trigonometric inequalities used by the converses

* `one_sub_sinc`: `1 - sin y / y ≥ min{y², 1}/8` for every real `y ≠ 0`. This is the inequality
  `1 - sinc y ≥ min{y^2, 1}/8` that turns the averaged characteristic function into a tail bound
  in the proof of Proposition "Strong converse with a reusable controller" (parts (b) and (c)).
* `one_sub_cos_le_abs` and `norm_exp_I_sub_one_sq`: `|e^{ix} - 1|^2 = 2 - 2cos x ≤ 2|x|`, the step
  behind the rotation bound `(1/2)‖α_t - α_C‖_1 ≤ √(2|t| s_n/β)` of Proposition "Unbalanced channels
  need a broad clock".
* `one_sub_cos_pow_le`: `1 - cos^n x ≤ n x^2/2`, used for the dephasing of the repetition code in
  Proposition "How large the clock must be" (d).
-/

namespace KeepingTime

open Real

lemma cos_le_quartic {x : ℝ} (hx : |x| ≤ 1) : cos x ≤ 1 - x ^ 2 / 2 + 5 / 96 * x ^ 4 := by
  have h := (abs_le.mp (Real.cos_bound hx)).2
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [h4] at h
  linarith

/-- `sin y ≤ y - y³/6 + y⁵/96` on `[0, 1]`, by integrating the quartic bound on `cos`. -/
lemma sin_le_quintic {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 96 := by
  let f : ℝ → ℝ := fun x => x - x ^ 3 / 6 + x ^ 5 / 96 - sin x
  have hderiv : ∀ x, HasDerivAt f (1 - x ^ 2 / 2 + 5 / 96 * x ^ 4 - cos x) x := by
    intro x
    have := (((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
      ((hasDerivAt_pow 5 x).div_const 96)).sub (hasDerivAt_sin x)
    convert this using 1
    norm_num
    ring
  have hmono : MonotoneOn f (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun x _ => (hderiv x).continuousAt.continuousWithinAt
    · exact fun x _ => (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x).deriv]
      have hc := cos_le_quartic (abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩)
      linarith
  have := hmono ⟨le_refl 0, zero_le_one⟩ ⟨h0, h1⟩ h0
  simp only [f, sin_zero] at this
  linarith

lemma sinc_tail_pos {y : ℝ} (hy : 0 < y) : y * (min (y ^ 2) 1 / 8) ≤ y - sin y := by
  rcases le_or_gt y 1 with h1 | h1
  · rw [min_eq_left (by nlinarith)]
    have hq := sin_le_quintic hy.le h1
    have h3 : 0 < y ^ 3 := pow_pos hy 3
    have h5 : y ^ 5 ≤ y ^ 3 := by
      have : y ^ 5 = y ^ 3 * y ^ 2 := by ring
      rw [this]
      exact mul_le_of_le_one_right h3.le (by nlinarith)
    have e : y * (y ^ 2 / 8) = y ^ 3 / 8 := by ring
    linarith
  · rw [min_eq_right (by nlinarith)]
    rcases le_or_gt (8 / 7) y with h2 | h2
    · have := sin_le_one y; linarith
    · -- 1 < y < 8/7: sin y - sin 1 = 2 sin((y-1)/2) cos((y+1)/2) ≤ (y - 1) cos 1
      have hsub := Real.sin_sub_sin y 1
      have ha : sin ((y - 1) / 2) ≤ (y - 1) / 2 := sin_le (by linarith)
      have ha0 : 0 ≤ sin ((y - 1) / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_gt_three])
      have hb0 : 0 ≤ cos ((y + 1) / 2) := cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
      have hb1 : cos ((y + 1) / 2) ≤ cos 1 :=
        cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three]) (by linarith)
      have hc1 : cos 1 ≤ 7 / 8 := by
        have := cos_le_quartic (x := 1) (by norm_num); linarith
      have hs1 : sin 1 ≤ 7 / 8 := by
        have := sin_le_quintic (y := 1) (by norm_num) (le_refl 1); linarith
      have hprod : sin ((y - 1) / 2) * cos ((y + 1) / 2) ≤ (y - 1) / 2 * (7 / 8) := by
        calc sin ((y - 1) / 2) * cos ((y + 1) / 2) ≤ (y - 1) / 2 * cos ((y + 1) / 2) :=
              mul_le_mul_of_nonneg_right ha hb0
          _ ≤ (y - 1) / 2 * (7 / 8) :=
              mul_le_mul_of_nonneg_left (hb1.trans hc1) (by linarith)
      nlinarith

lemma one_sub_sinc_pos {y : ℝ} (hy : 0 < y) : min (y ^ 2) 1 / 8 ≤ 1 - sin y / y := by
  have h := sinc_tail_pos hy
  have : sin y / y ≤ 1 - min (y ^ 2) 1 / 8 := by
    rw [div_le_iff₀ hy]
    nlinarith
  linarith

/-- `1 - sinc y ≥ min{y², 1}/8` for every real `y ≠ 0`. -/
theorem one_sub_sinc (y : ℝ) (hy : y ≠ 0) : min (y ^ 2) 1 / 8 ≤ 1 - sin y / y := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have h := one_sub_sinc_pos (neg_pos.mpr hneg)
    rwa [neg_sq, sin_neg, neg_div_neg_eq] at h
  · exact one_sub_sinc_pos hpos

/-- `1 - cos x ≤ |x|` for every real `x`. -/
theorem one_sub_cos_le_abs (x : ℝ) : 1 - cos x ≤ |x| := by
  rcases le_or_gt |x| 2 with h | h
  · have h1 : 1 - x ^ 2 / 2 ≤ cos x := Real.one_sub_sq_div_two_le_cos
    have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [abs_nonneg x]
  · have := Real.neg_one_le_cos x
    linarith

/-- `|e^{ix} - 1|² = 2 - 2 cos x ≤ 2|x|`. -/
theorem norm_exp_I_sub_one_sq (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 = 2 - 2 * cos x ∧
      ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 ≤ 2 * |x| := by
  have e : Complex.exp (x * Complex.I) - 1 = ((cos x - 1 : ℝ) : ℂ) + ((sin x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hn : ‖Complex.exp (x * Complex.I) - 1‖ ^ 2 = 2 - 2 * cos x := by
    rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith [sin_sq_add_cos_sq x]
  refine ⟨hn, ?_⟩
  rw [hn]
  have := one_sub_cos_le_abs x
  linarith

/-- `1 - cos^n x ≤ n x²/2` for every real `x` (Bernoulli's inequality and `1 - cos x ≤ x²/2`). -/
theorem one_sub_cos_pow_le (x : ℝ) (n : ℕ) : 1 - cos x ^ n ≤ n * x ^ 2 / 2 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ cos x - 1 by linarith [neg_one_le_cos x]) n
  have hc : 1 - x ^ 2 / 2 ≤ cos x := Real.one_sub_sq_div_two_le_cos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [add_sub_cancel] at hb
  nlinarith

end KeepingTime

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms KeepingTime.one_sub_sinc
#print axioms KeepingTime.one_sub_cos_le_abs
#print axioms KeepingTime.norm_exp_I_sub_one_sq
#print axioms KeepingTime.one_sub_cos_pow_le
