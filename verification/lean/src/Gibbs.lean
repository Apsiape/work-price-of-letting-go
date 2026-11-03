import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Field

/-!
# The finite Gibbs variational principle and its uses

Natural logarithms throughout.  For a probability vector `p` on a finite type and real energies `E`,

* `gibbs_variational`: `∑ negMulLog (p i) ≤ ∑ p i * E i + log ∑ exp (-E i)`;
* `gibbs_attains`: equality at the Gibbs vector `exp (-E i) / Z`.

Uses in the manuscript:

* the delay process (Section 7): `binEntropy p - x p ≤ log (1 + e^{-x})`, attained at the Gibbs state
  `p = e^{-x}/(1 + e^{-x})`, while the two terms maximized separately give `log 2`, which is larger for `x > 0`
  (`delay_value_le`, `delay_value_attained`, `separate_maxima`, `delay_value_lt_log_two`);
* Appendix B.7: an integer-valued variable with second moment `μ` has entropy at most
  `λ μ + log ∑ exp (-λ b²)` (`entropy_le_second_moment`).
-/

open Real

namespace Gibbs

variable {ι : Type*} [Fintype ι]

theorem gibbs_variational (p E : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, negMulLog (p i) ≤ ∑ i, p i * E i + log (∑ i, exp (-E i)) := by
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsum
  have hZ : 0 < ∑ i, exp (-E i) := Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
  set Z := ∑ i, exp (-E i) with hZdef
  -- termwise: negMulLog p - p E - p log Z ≤ q - p, with q = exp(-E)/Z
  have key : ∀ i, negMulLog (p i) - p i * E i - p i * log Z ≤ exp (-E i) / Z - p i := by
    intro i
    rcases (hp i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp; positivity
    · have hq : 0 < exp (-E i) / Z := div_pos (exp_pos _) hZ
      have hlog : log (exp (-E i) / Z / p i) ≤ exp (-E i) / Z / p i - 1 :=
        log_le_sub_one_of_pos (div_pos hq hpos)
      have hsplit : log (exp (-E i) / Z / p i) = -E i - log Z - log (p i) := by
        rw [log_div hq.ne' hpos.ne', log_div (exp_pos _).ne' hZ.ne', log_exp]
      rw [hsplit] at hlog
      have h1 : p i * (-E i - log Z - log (p i)) ≤ p i * (exp (-E i) / Z / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog hpos.le
      have h2 : p i * (exp (-E i) / Z / p i - 1) = exp (-E i) / Z - p i := by
        field_simp
      rw [negMulLog]
      nlinarith [h1, h2]
  have hsumq : ∑ i, exp (-E i) / Z = 1 := by
    rw [← Finset.sum_div, div_self hZ.ne']
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  simp only [Finset.sum_sub_distrib, hsumq, hsum, ← Finset.sum_mul] at this
  linarith

theorem gibbs_attains (E : ι → ℝ) [Nonempty ι] :
    ∑ i, negMulLog (exp (-E i) / ∑ j, exp (-E j))
      = ∑ i, (exp (-E i) / ∑ j, exp (-E j)) * E i + log (∑ j, exp (-E j)) := by
  have hZ : 0 < ∑ j, exp (-E j) := Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
  set Z := ∑ j, exp (-E j)
  have hsumq : ∑ i, exp (-E i) / Z = 1 := by rw [← Finset.sum_div, div_self hZ.ne']
  have : ∀ i, negMulLog (exp (-E i) / Z) = exp (-E i) / Z * E i + exp (-E i) / Z * log Z := by
    intro i
    rw [negMulLog, log_div (exp_pos _).ne' hZ.ne', log_exp]
    ring
  simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hsumq, one_mul]

/-- The delay process: the score `S(ρ_{I_2}) - β E ⟨1|ρ_{I_2}|1⟩` (nats, `x = βE`) is at most `log (1 + e^{-x})`. -/
theorem delay_value_le (x p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    binEntropy p - x * p ≤ log (1 + exp (-x)) := by
  have h := gibbs_variational (ι := Fin 2) ![1 - p, p] ![0, x]
    (by intro i; fin_cases i <;> simp <;> linarith) (by simp)
  simp [Fin.sum_univ_two] at h
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

/-- The maximum is attained at the Gibbs state. -/
theorem delay_value_attained (x : ℝ) :
    binEntropy (exp (-x) / (1 + exp (-x))) - x * (exp (-x) / (1 + exp (-x))) = log (1 + exp (-x)) := by
  have h := gibbs_attains (ι := Fin 2) ![0, x]
  simp [Fin.sum_univ_two] at h
  have hq : 1 - exp (-x) / (1 + exp (-x)) = 1 / (1 + exp (-x)) := by
    have : (1 + exp (-x)) ≠ 0 := by positivity
    field_simp
    ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq]
  have e1 : (1 : ℝ) / (1 + exp (-x)) = (1 + exp (-x))⁻¹ := one_div _
  rw [e1]
  have e2 : exp (-x) / (1 + exp (-x)) = exp (-x) * (1 + exp (-x))⁻¹ := div_eq_mul_inv _ _
  rw [e2] at h ⊢
  linarith

/-- Taken separately, the entropy term is largest at `p = 1/2` (value `log 2`) and the energy term at `p = 0`
(value `0`): the separate maxima add up to `log 2`. -/
theorem separate_maxima (x p : ℝ) (hx : 0 ≤ x) (h0 : 0 ≤ p) :
    binEntropy p ≤ log 2 ∧ binEntropy 2⁻¹ = log 2 ∧ -(x * p) ≤ 0 ∧ -(x * 0) = 0 := by
  refine ⟨binEntropy_le_log_two, binEntropy_two_inv, ?_, by ring⟩
  have := mul_nonneg hx h0
  linarith

theorem delay_value_lt_log_two (x : ℝ) (hx : 0 < x) : log (1 + exp (-x)) < log 2 := by
  have : exp (-x) < 1 := by rw [exp_lt_one_iff]; linarith
  exact log_lt_log (by positivity) (by linarith)

/-- Appendix B.7: entropy of an integer-valued variable (finite support) with second moment `μ`. -/
theorem entropy_le_second_moment (p : ι → ℝ) (b : ι → ℤ) (lam : ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ∑ i, negMulLog (p i) ≤ lam * (∑ i, p i * (b i : ℝ) ^ 2) + log (∑ i, exp (-(lam * (b i : ℝ) ^ 2))) := by
  have h := gibbs_variational p (fun i => lam * (b i : ℝ) ^ 2) hp hsum
  have e : ∑ i, p i * (lam * (b i : ℝ) ^ 2) = lam * ∑ i, p i * (b i : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  linarith [e]

end Gibbs

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Gibbs.gibbs_variational
#print axioms Gibbs.gibbs_attains
#print axioms Gibbs.delay_value_le
#print axioms Gibbs.delay_value_attained
#print axioms Gibbs.separate_maxima
#print axioms Gibbs.delay_value_lt_log_two
#print axioms Gibbs.entropy_le_second_moment
