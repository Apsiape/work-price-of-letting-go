import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The correlated process with hidden memory (Section 7)

With `v_t = (E/2) √(3/2 + cos 2t + sin 2t)`:

* `vt_lt_branchwise`: for `0 < t < π/8`, `3/2 + cos 2t + sin 2t < (1 + 1/√2)²`, so `v_t < (E/2)(1 + 1/√2)`, the
  branchwise worst case: a device that pays each branch's worst case overpays;
* `vt_at_pi_div_eight`: equality at `t = π/8`, where the fidelity constraint stops binding;
* `overlap_ge_cos`: the purified overlap of the two branches, `|cos t + i sin t ⟨Z⟩|`, is at least `|cos t|` (the
  root-fidelity condition), with equality when `⟨Z⟩ = 0`;
* `period_pi`: `e^{i(t+π)Z} = -e^{itZ}`, so the process depends on `t` only modulo `π`.
-/

open Real

namespace HiddenBit

lemma branchwise_sq : (1 + 1 / √2) ^ 2 = 3 / 2 + √2 := by
  have h2 : (√2) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hpos : 0 < √2 := by positivity
  field_simp
  nlinarith [h2]

theorem vt_lt_branchwise (t : ℝ) (h0 : 0 < t) (h1 : t < π / 8) :
    3 / 2 + cos (2 * t) + sin (2 * t) < (1 + 1 / √2) ^ 2 := by
  rw [branchwise_sq]
  have hpi := pi_pos
  -- (cos x + sin x)^2 = 1 + sin 2x with x = 2t, and sin 4t < 1 because 0 < 4t < π/2
  have hsin4 : sin (2 * (2 * t)) < 1 := by
    have hmem1 : 2 * (2 * t) ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
    have hmem2 : π / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, le_rfl⟩
    have := strictMonoOn_sin hmem1 hmem2 (by linarith)
    rwa [sin_pi_div_two] at this
  have hsq : (cos (2 * t) + sin (2 * t)) ^ 2 < 2 := by
    have e : (cos (2 * t) + sin (2 * t)) ^ 2 = 1 + sin (2 * (2 * t)) := by
      have hs : sin (2 * (2 * t)) = 2 * sin (2 * t) * cos (2 * t) := sin_two_mul (2 * t)
      linear_combination sin_sq_add_cos_sq (2 * t) - hs
    rw [e]; linarith
  have hlt : cos (2 * t) + sin (2 * t) < √2 := by
    by_cases hnn : 0 ≤ cos (2 * t) + sin (2 * t)
    · exact (lt_sqrt hnn).mpr hsq
    · push Not at hnn; exact lt_of_lt_of_le hnn (sqrt_nonneg 2)
  linarith

theorem vt_at_pi_div_eight : 3 / 2 + cos (2 * (π / 8)) + sin (2 * (π / 8)) = (1 + 1 / √2) ^ 2 := by
  rw [branchwise_sq, show 2 * (π / 8) = π / 4 by ring, cos_pi_div_four, sin_pi_div_four]
  ring

theorem overlap_ge_cos (t z : ℝ) : |cos t| ≤ √((cos t) ^ 2 + (sin t * z) ^ 2) := by
  rw [← sqrt_sq_eq_abs]
  exact sqrt_le_sqrt (by nlinarith [sq_nonneg (sin t * z)])

theorem period_pi (t : ℝ) : Complex.exp (((t + π : ℝ) : ℂ) * Complex.I) = -Complex.exp ((t : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

end HiddenBit

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms HiddenBit.branchwise_sq
#print axioms HiddenBit.vt_lt_branchwise
#print axioms HiddenBit.vt_at_pi_div_eight
#print axioms HiddenBit.overlap_ge_cos
#print axioms HiddenBit.period_pi
