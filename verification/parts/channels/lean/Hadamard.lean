import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The returning-clock bound for the Hadamard gate (Proposition "A returning clock")

The ideal output `|+⟩^{⊗n}` has weight `2^{-n} C(n,k)` in the sector with `k` excitations: the
basis strings with `k` excitations are the `k`-subsets of the `n` sites (`sector_card`).  A
real output that commutes with the total energy passes the test for `|+⟩^{⊗n}` with
probability at most `max_k 2^{-n} C(n,k)`, and the largest binomial coefficient is the middle
one (`sector_le_middle`), so the error is at least `1 - 2^{-n} C(n, ⌊n/2⌋)`.

We prove `(n + 1) C(n, ⌊n/2⌋)^2 ≤ 4^n` for every `n` (`middle_sq_le`), hence
`2^{-n} C(n, ⌊n/2⌋) ≤ 1/√(n+1)` (`middle_weight_le`), so the bound tends to one.
-/

namespace Hadamard

open Finset

/-- The number of basis strings of `n` qubits with exactly `k` excitations is `C(n, k)`. -/
theorem sector_card (n k : ℕ) :
    (univ.filter (fun s : Finset (Fin n) => s.card = k)).card = n.choose k := by
  rw [← powerset_univ, ← powersetCard_eq_filter, card_powersetCard, card_univ, Fintype.card_fin]

/-- The middle binomial coefficient is the largest. -/
theorem sector_le_middle (n k : ℕ) : n.choose k ≤ n.choose (n / 2) :=
  Nat.choose_le_middle k n

/-- The error bound `1 - 2^{-n} C(n,k)` is smallest at the middle sector. -/
theorem error_bound_middle (n k : ℕ) :
    1 - (n.choose (n / 2) : ℝ) / 2 ^ n ≤ 1 - (n.choose k : ℝ) / 2 ^ n := by
  have h : (n.choose k : ℝ) ≤ n.choose (n / 2) := by exact_mod_cast sector_le_middle n k
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have := div_le_div_of_nonneg_right h hp.le
  linarith

/-- `(2m+1) C(2m, m)^2 ≤ 16^m`. -/
theorem central_sq_le (m : ℕ) : (2 * m + 1) * m.centralBinom ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrec := Nat.succ_mul_centralBinom_succ m
    set A := m.centralBinom
    set B := (m + 1).centralBinom
    -- multiply the goal by (m+1)^2
    have key : (m + 1) ^ 2 * ((2 * (m + 1) + 1) * B ^ 2) ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
      have e1 : (m + 1) ^ 2 * ((2 * (m + 1) + 1) * B ^ 2) = (2 * m + 3) * ((m + 1) * B) ^ 2 := by ring
      rw [e1, hrec]
      have e2 : (2 * m + 3) * (2 * (2 * m + 1) * A) ^ 2
          = 4 * ((2 * m + 3) * (2 * m + 1)) * ((2 * m + 1) * A ^ 2) := by ring
      rw [e2]
      have h1 : (2 * m + 3) * (2 * m + 1) ≤ 4 * (m + 1) ^ 2 := by nlinarith
      calc 4 * ((2 * m + 3) * (2 * m + 1)) * ((2 * m + 1) * A ^ 2)
          ≤ 4 * (4 * (m + 1) ^ 2) * 16 ^ m := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) ih
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- `(n + 1) C(n, ⌊n/2⌋)^2 ≤ 4^n` for every `n`. -/
theorem middle_sq_le (n : ℕ) : (n + 1) * (n.choose (n / 2)) ^ 2 ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h2 : 2 * m / 2 = m := by omega
    rw [h2]
    have := central_sq_le m
    rw [Nat.centralBinom_eq_two_mul_choose] at this
    calc (2 * m + 1) * ((2 * m).choose m) ^ 2 ≤ 16 ^ m := this
      _ = 4 ^ (2 * m) := by rw [pow_mul]; norm_num
  · have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h2]
    -- C(2m+2, m+1) = 2 C(2m+1, m)
    have hsplit : (m + 1).centralBinom = 2 * (2 * m + 1).choose m := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      have : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    have h := central_sq_le (m + 1)
    rw [hsplit] at h
    set D := (2 * m + 1).choose m
    have h' : 4 * ((2 * m + 3) * D ^ 2) ≤ 4 * 4 ^ (2 * m + 1) := by
      calc 4 * ((2 * m + 3) * D ^ 2) = (2 * (m + 1) + 1) * (2 * D) ^ 2 := by ring
        _ ≤ 16 ^ (m + 1) := h
        _ = 4 * 4 ^ (2 * m + 1) := by rw [show 16 = 4 ^ 2 by norm_num, ← pow_mul]; ring
    have h'' : (2 * m + 3) * D ^ 2 ≤ 4 ^ (2 * m + 1) := Nat.le_of_mul_le_mul_left h' (by norm_num)
    calc (2 * m + 1 + 1) * D ^ 2 ≤ (2 * m + 3) * D ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 4 ^ (2 * m + 1) := h''

/-- The weight of the middle sector is at most `1/√(n+1)`, so the error bound
`1 - 2^{-n} C(n, ⌊n/2⌋)` is at least `1 - 1/√(n+1)` and tends to one. -/
theorem middle_weight_le (n : ℕ) :
    (n.choose (n / 2) : ℝ) / 2 ^ n ≤ 1 / Real.sqrt (n + 1) := by
  have hsq : ((n + 1 : ℕ) : ℝ) * ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 ≤ ((4 ^ n : ℕ) : ℝ) := by
    exact_mod_cast middle_sq_le n
  push_cast at hsq
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (0 : ℝ) ≤ (n.choose (n / 2) : ℝ) / 2 ^ n := by positivity
  have hs : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hpos
  rw [le_div_iff₀ hs]
  have hsq' : ((n.choose (n / 2) : ℝ) / 2 ^ n * Real.sqrt ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hpos.le]
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    have : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    nlinarith [this]
  have hnn : 0 ≤ (n.choose (n / 2) : ℝ) / 2 ^ n * Real.sqrt ((n : ℝ) + 1) := by positivity
  nlinarith [hsq', hnn]

/-- The error lower bound of the proposition, in its final form: for every `n`,
`1 - 2^{-n} C(n, ⌊n/2⌋) ≥ 1 - 1/√(n+1)`. -/
theorem error_ge (n : ℕ) :
    1 - 1 / Real.sqrt (n + 1) ≤ 1 - (n.choose (n / 2) : ℝ) / 2 ^ n := by
  have := middle_weight_le n
  linarith

end Hadamard

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Hadamard.sector_card
#print axioms Hadamard.sector_le_middle
#print axioms Hadamard.error_bound_middle
#print axioms Hadamard.central_sq_le
#print axioms Hadamard.middle_sq_le
#print axioms Hadamard.middle_weight_le
#print axioms Hadamard.error_ge
