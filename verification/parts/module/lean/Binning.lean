import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# One offset for all contacts: the binning inequality (Appendix D, Step 3)

Two eigenvalues `λ_a, λ_b` of the source, written `x = ln(λ_a/λ_b)`, fall into different bins of width `h` with
probability `min{1, |x|/h}` over a uniform offset.  The manuscript bounds this by
`|sqrt(λ_a/λ_b) - 1| / (1 - e^{-h/2})`, that is, by `|e^{x/2} - 1| / (1 - e^{-h/2})`.  We prove

* `binning`: `min 1 (|x|/h) * (1 - exp (-h/2)) ≤ |exp (x/2) - 1|` for every real `x` and `h > 0`;
* `binning_div`: the same inequality in the divided form used in the text.
-/

open Real

namespace Binning

lemma one_sub_exp_neg_le (u : ℝ) : 1 - exp (-u) ≤ u := by
  have := add_one_le_exp (-u)
  linarith

theorem binning (x h : ℝ) (hh : 0 < h) :
    min 1 (|x| / h) * (1 - exp (-(h / 2))) ≤ |exp (x / 2) - 1| := by
  have hc : 0 < 1 - exp (-(h / 2)) := by
    have : exp (-(h / 2)) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith
  rcases le_or_gt 0 x with hx | hx
  · -- x ≥ 0: min ≤ x/h, (1 - e^{-h/2}) ≤ h/2, and x/2 ≤ e^{x/2} - 1
    have h1 : min 1 (|x| / h) ≤ x / h := by rw [abs_of_nonneg hx]; exact min_le_right _ _
    have h2 : 1 - exp (-(h / 2)) ≤ h / 2 := one_sub_exp_neg_le _
    have h3 : x / 2 ≤ exp (x / 2) - 1 := by have := add_one_le_exp (x / 2); linarith
    have h4 : 0 ≤ exp (x / 2) - 1 := by linarith
    rw [abs_of_nonneg h4]
    calc min 1 (|x| / h) * (1 - exp (-(h / 2))) ≤ x / h * (h / 2) := by
          apply mul_le_mul h1 h2 hc.le (div_nonneg hx hh.le)
      _ = x / 2 := by field_simp
      _ ≤ exp (x / 2) - 1 := h3
  · have hneg : exp (x / 2) - 1 < 0 := by
      have : exp (x / 2) < 1 := by rw [exp_lt_one_iff]; linarith
      linarith
    rw [abs_of_neg hneg, abs_of_neg hx]
    rcases le_or_gt h (-x) with hxh | hxh
    · -- |x| ≥ h: the minimum is 1 and 1 - e^{x/2} ≥ 1 - e^{-h/2}
      have hmin : min 1 (-x / h) = 1 := by
        apply min_eq_left; rw [le_div_iff₀ hh]; linarith
      rw [hmin, one_mul]
      have : exp (x / 2) ≤ exp (-(h / 2)) := exp_le_exp.mpr (by linarith)
      linarith
    · -- |x| < h: concavity of 1 - e^{-u/2} between 0 and h
      have hmin : min 1 (-x / h) = -x / h := by
        apply min_eq_right; rw [div_le_iff₀ hh]; linarith
      rw [hmin]
      set t := -x / h with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hh.le
      have ht1 : t ≤ 1 := by rw [ht, div_le_iff₀ hh]; linarith
      -- e^{x/2} = exp(t * (-(h/2)) + (1 - t) * 0) ≤ t e^{-h/2} + (1 - t)
      have hconv := convexOn_exp.2 (Set.mem_univ (-(h / 2))) (Set.mem_univ (0 : ℝ)) ht0 (by linarith : 0 ≤ 1 - t)
        (by ring : t + (1 - t) = 1)
      have harg : t • (-(h / 2)) + (1 - t) • (0 : ℝ) = x / 2 := by
        simp only [smul_eq_mul, mul_zero, add_zero]
        rw [ht]; field_simp
      rw [harg] at hconv
      simp only [smul_eq_mul, exp_zero, mul_one] at hconv
      nlinarith [hconv]

theorem binning_div (x h : ℝ) (hh : 0 < h) :
    min 1 (|x| / h) ≤ |exp (x / 2) - 1| / (1 - exp (-(h / 2))) := by
  have hc : 0 < 1 - exp (-(h / 2)) := by
    have : exp (-(h / 2)) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith
  rw [le_div_iff₀ hc]
  exact binning x h hh

end Binning

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Binning.one_sub_exp_neg_le
#print axioms Binning.binning
#print axioms Binning.binning_div
