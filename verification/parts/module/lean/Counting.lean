import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Counting tested outcome strings (Appendix C.3)

The event `G` allows at most `2γN` tested episodes, each with one of `L` outcomes.  The number of such outcome
strings is `Σ_{k ≤ 2γN} C(N,k) L^k`, and the manuscript bounds it by `2^{N θ_γ}` with
`θ_γ = h(2γ) + 2γ log2 L`.  In natural logarithms, with `α = 2γ ≤ 1/2`:

* `count_bound`: `Σ_{k ≤ K} C(N,k) L^k ≤ exp(N h(α)) L^{αN}` whenever `K ≤ αN`, `0 < α ≤ 1/2` and `L ≥ 1`.
-/

open Real

namespace Counting

theorem count_bound (N K : ℕ) (L α : ℝ) (hL : 1 ≤ L) (hα0 : 0 < α) (hα : α ≤ 1 / 2) (hK : (K : ℝ) ≤ α * N) :
    ∑ k ∈ Finset.range (K + 1), (N.choose k : ℝ) * L ^ k ≤ exp (N * binEntropy α) * L ^ (α * N) := by
  have hα1 : 0 < 1 - α := by linarith
  have hLpos : 0 < L := by linarith
  set y := α / (L * (1 - α)) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one (by positivity)]
    nlinarith
  have hKN : K ≤ N := by
    have : (K : ℝ) ≤ N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact_mod_cast this
  -- each term is at most C(N,k) (L y)^k y^{-αN}
  have hterm : ∀ k ∈ Finset.range (K + 1),
      (N.choose k : ℝ) * L ^ k ≤ (N.choose k : ℝ) * (L * y) ^ k * y ^ (-(α * N)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ α * N := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hK
    have hpow : 1 ≤ y ^ ((k : ℝ) - α * N) := one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by linarith)
    have hsplit : (L * y) ^ k * y ^ (-(α * N)) = L ^ k * y ^ ((k : ℝ) - α * N) := by
      rw [mul_pow, sub_eq_add_neg, rpow_add hy0, rpow_natCast]
      ring
    rw [mul_assoc, hsplit]
    have : 0 ≤ (N.choose k : ℝ) * L ^ k := by positivity
    nlinarith
  calc ∑ k ∈ Finset.range (K + 1), (N.choose k : ℝ) * L ^ k
      ≤ ∑ k ∈ Finset.range (K + 1), (N.choose k : ℝ) * (L * y) ^ k * y ^ (-(α * N)) := Finset.sum_le_sum hterm
    _ ≤ ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (L * y) ^ k * y ^ (-(α * N)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_subset_range.mpr (by omega)
        · intro k _ _; positivity
    _ = (1 + L * y) ^ N * y ^ (-(α * N)) := by
        rw [← Finset.sum_mul, show (1 + L * y) = L * y + 1 by ring, add_pow]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [one_pow, mul_one, mul_comm]
    _ = exp (N * binEntropy α) * L ^ (α * N) := by
        have hLy : 1 + L * y = (1 - α)⁻¹ := by
          rw [hy]; field_simp; ring
        rw [hLy]
        have e1 : ((1 - α)⁻¹) ^ N = exp (-(N * log (1 - α))) := by
          rw [exp_neg, ← log_pow, exp_log (by positivity), inv_pow]
        have e2 : y ^ (-(α * N)) = L ^ (α * N) * exp (α * N * (log (1 - α) - log α)) := by
          rw [hy, rpow_neg (by positivity), ← inv_rpow (by positivity), inv_div,
            mul_div_assoc, mul_rpow hLpos.le (by positivity), rpow_def_of_pos (div_pos hα1 hα0),
            log_div hα1.ne' hα0.ne']
          ring_nf
        rw [e1, e2, binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
        rw [mul_comm (L ^ (α * N)), ← mul_assoc, ← exp_add]
        congr 2
        ring

end Counting

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Counting.count_bound
