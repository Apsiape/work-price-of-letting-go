import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# The ladder that pays a battery

These are the finite and trigonometric steps of part (c) of Corollary "A controller returned only in state is a
second battery" and its appendix proof.

* `pay`: basis states `|l⟩_L |b⟩_{W_2}` with ladder level `l` (energy `l` in units of `ω`) and register bit `b`
  (energy `k` when set). The map exchanging `|k + j, 0⟩` with `|j, 1⟩` for `1 ≤ j ≤ N`, and fixing every other basis
  state, conserves energy (`pay_energy`), is an involution (`pay_pay`), hence a permutation, and never leaves the
  ladder of levels `1, …, k + N` (`pay_level`).
* `sine_rec`, `shift_sum`, `sine_shift`: the sine coefficients `a_j = sin(jθ)` with `θ = π/(N+1)` satisfy
  `a_{j-1} + a_{j+1} = 2 cos θ · a_j` and `a_0 = a_{N+1} = 0`, so
  `2 Σ_{j=1}^{N-1} a_j a_{j+1} = 2 cos θ · Σ_{j=1}^{N} a_j²`: the packet's overlap with its one-level shift is
  `cos θ` times its squared norm.
* `two_sub_two_cos_le`: `2 - 2 cos θ ≤ θ²`, so one shift moves the normalized packet by at most `θ`.
* `choice_of_N`, `range_of_ladder`: for the pure ladder, with `N = ⌈kπ/η⌉₊`, the bound `kπ/(N+1) ≤ η` holds and the
  ladder's range `k + N - 1` is at most `(1 + π/η) k`.
* `choice_of_N_diag`, `N_ge_k`, `range_of_ladder_diag`: for the classical ladder, a uniform mixture of `N` levels
  shifted by `k` levels, with `N = ⌈k/η⌉₊`: the shift `k/N` is at most `η`, `N ≥ k` when `η ≤ 1`, and the range
  `k + N - 1` is at most `(1 + 1/η) k`.
-/

namespace KeepingTime

namespace Ladder

/-- Energy of `|l⟩_L |b⟩_{W_2}` in units of `ω`. -/
def energy (k : ℕ) (s : ℕ × Bool) : ℕ := s.1 + (if s.2 then k else 0)

/-- The payment swap. -/
def pay (k N : ℕ) : ℕ × Bool → ℕ × Bool
  | (l, false) => if k + 1 ≤ l ∧ l ≤ k + N then (l - k, true) else (l, false)
  | (l, true) => if 1 ≤ l ∧ l ≤ N then (l + k, false) else (l, true)

theorem pay_energy (k N : ℕ) (s : ℕ × Bool) : energy k (pay k N s) = energy k s := by
  obtain ⟨l, b⟩ := s
  cases b with
  | false =>
    simp only [pay]
    split_ifs with h
    · simp [energy]
      omega
    · rfl
  | true =>
    simp only [pay]
    split_ifs with h
    · simp [energy]
    · rfl

theorem pay_pay (k N : ℕ) (s : ℕ × Bool) : pay k N (pay k N s) = s := by
  obtain ⟨l, b⟩ := s
  cases b with
  | false =>
    by_cases h : k + 1 ≤ l ∧ l ≤ k + N
    · have h' : 1 ≤ l - k ∧ l - k ≤ N := by omega
      simp only [pay, h, h', and_self, if_true]
      congr 1
      omega
    · simp only [pay, h, if_false]
  | true =>
    by_cases h : 1 ≤ l ∧ l ≤ N
    · have h' : k + 1 ≤ l + k ∧ l + k ≤ k + N := by omega
      simp only [pay, h, h', and_self, if_true]
      congr 1
      omega
    · simp only [pay, h, if_false]

theorem pay_level (k N : ℕ) (s : ℕ × Bool) (h1 : 1 ≤ s.1) (h2 : s.1 ≤ k + N) :
    1 ≤ (pay k N s).1 ∧ (pay k N s).1 ≤ k + N := by
  obtain ⟨l, b⟩ := s
  simp only at h1 h2
  cases b with
  | false =>
    simp only [pay]
    split_ifs with h
    · simp only; omega
    · simp only; omega
  | true =>
    simp only [pay]
    split_ifs with h
    · simp only; omega
    · simp only; omega

/-- The three-term recurrence of the sine coefficients. -/
theorem sine_rec (θ : ℝ) (j : ℕ) :
    Real.sin ((j : ℝ) * θ) + Real.sin (((j : ℝ) + 2) * θ)
      = 2 * Real.cos θ * Real.sin (((j : ℝ) + 1) * θ) := by
  have h1 : (j : ℝ) * θ = ((j : ℝ) + 1) * θ - θ := by ring
  have h2 : ((j : ℝ) + 2) * θ = ((j : ℝ) + 1) * θ + θ := by ring
  rw [h1, h2, Real.sin_sub, Real.sin_add]
  ring

/-- A sequence with vanishing ends and a three-term recurrence has `2 Σ a_j a_{j+1} = c Σ a_j²`. -/
theorem shift_sum (a : ℕ → ℝ) (c : ℝ) (N : ℕ) (h0 : a 0 = 0) (hN : a (N + 1) = 0)
    (hrec : ∀ j, a j + a (j + 2) = c * a (j + 1)) :
    2 * ∑ j ∈ Finset.range N, a (j + 1) * a (j + 2)
      = c * ∑ j ∈ Finset.range N, a (j + 1) ^ 2 := by
  have hsplit : ∑ j ∈ Finset.range N, a (j + 1) * a j
      = ∑ j ∈ Finset.range N, a (j + 1) * a (j + 2) := by
    have e1 := Finset.sum_range_succ (fun j => a j * a (j + 1)) N
    have e2 := Finset.sum_range_succ' (fun j => a j * a (j + 1)) N
    simp only [hN, mul_zero, add_zero, h0, zero_mul] at e1 e2
    have : ∑ j ∈ Finset.range N, a j * a (j + 1)
        = ∑ j ∈ Finset.range N, a (j + 1) * a (j + 1 + 1) := by rw [← e1, e2]
    calc ∑ j ∈ Finset.range N, a (j + 1) * a j
        = ∑ j ∈ Finset.range N, a j * a (j + 1) := by
          apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ j ∈ Finset.range N, a (j + 1) * a (j + 1 + 1) := this
      _ = ∑ j ∈ Finset.range N, a (j + 1) * a (j + 2) := rfl
  have hrec' : ∑ j ∈ Finset.range N, a (j + 1) * (a j + a (j + 2))
      = c * ∑ j ∈ Finset.range N, a (j + 1) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hrec j]
    ring
  have hexp : ∑ j ∈ Finset.range N, a (j + 1) * (a j + a (j + 2))
      = ∑ j ∈ Finset.range N, a (j + 1) * a j
        + ∑ j ∈ Finset.range N, a (j + 1) * a (j + 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp, hsplit] at hrec'
  linarith

/-- The sine packet on `N` levels: its overlap with its one-level shift is `cos(π/(N+1))` times its squared norm. -/
theorem sine_shift (N : ℕ) :
    2 * ∑ j ∈ Finset.range N,
        Real.sin (((j : ℝ) + 1) * (Real.pi / ((N : ℝ) + 1)))
          * Real.sin (((j : ℝ) + 2) * (Real.pi / ((N : ℝ) + 1)))
      = 2 * Real.cos (Real.pi / ((N : ℝ) + 1))
          * ∑ j ∈ Finset.range N, Real.sin (((j : ℝ) + 1) * (Real.pi / ((N : ℝ) + 1))) ^ 2 := by
  set θ := Real.pi / ((N : ℝ) + 1) with hθ
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have key := shift_sum (fun j : ℕ => Real.sin ((j : ℝ) * θ)) (2 * Real.cos θ) N
    (by simp) (by
      simp only [Nat.cast_add, Nat.cast_one]
      have : ((N : ℝ) + 1) * θ = Real.pi := by rw [hθ]; field_simp
      rw [this, Real.sin_pi])
    (by
      intro j
      have := sine_rec θ j
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      linarith)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using key

theorem two_sub_two_cos_le (θ : ℝ) : 2 - 2 * Real.cos θ ≤ θ ^ 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

theorem choice_of_N (k : ℕ) (η : ℝ) (hη : 0 < η) :
    (k : ℝ) * Real.pi / ((⌈(k : ℝ) * Real.pi / η⌉₊ : ℕ) + 1 : ℝ) ≤ η := by
  have hle : (k : ℝ) * Real.pi / η ≤ (⌈(k : ℝ) * Real.pi / η⌉₊ : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < (⌈(k : ℝ) * Real.pi / η⌉₊ : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  have h2 : (k : ℝ) * Real.pi ≤ η * (⌈(k : ℝ) * Real.pi / η⌉₊ : ℝ) := by
    rwa [div_le_iff₀' hη] at hle
  nlinarith

theorem range_of_ladder (k : ℕ) (η : ℝ) (hη : 0 < η) :
    (k : ℝ) + (⌈(k : ℝ) * Real.pi / η⌉₊ : ℝ) - 1 ≤ (1 + Real.pi / η) * k := by
  have h0 : 0 ≤ (k : ℝ) * Real.pi / η := by positivity
  have hlt := Nat.ceil_lt_add_one (R := ℝ) h0
  have : (1 + Real.pi / η) * k = k + (k : ℝ) * Real.pi / η := by ring
  rw [this]
  linarith

theorem choice_of_N_diag (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) :
    (k : ℝ) / (⌈(k : ℝ) / η⌉₊ : ℝ) ≤ η := by
  have hle : (k : ℝ) / η ≤ (⌈(k : ℝ) / η⌉₊ : ℝ) := Nat.le_ceil _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (⌈(k : ℝ) / η⌉₊ : ℝ) := lt_of_lt_of_le (div_pos hkpos hη) hle
  rw [div_le_iff₀ hpos]
  have h2 : (k : ℝ) ≤ η * (⌈(k : ℝ) / η⌉₊ : ℝ) := by
    rwa [div_le_iff₀' hη] at hle
  linarith

theorem N_ge_k (k : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : k ≤ ⌈(k : ℝ) / η⌉₊ := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : (k : ℝ) ≤ (k : ℝ) / η := by
    rw [le_div_iff₀ hη]
    nlinarith
  exact_mod_cast this.trans (Nat.le_ceil _)

theorem range_of_ladder_diag (k : ℕ) (η : ℝ) (hη : 0 < η) :
    (k : ℝ) + (⌈(k : ℝ) / η⌉₊ : ℝ) - 1 ≤ (1 + 1 / η) * k := by
  have h0 : 0 ≤ (k : ℝ) / η := by positivity
  have hlt := Nat.ceil_lt_add_one (R := ℝ) h0
  have : (1 + 1 / η) * k = k + (k : ℝ) / η := by ring
  rw [this]
  linarith

end Ladder

end KeepingTime

#print axioms KeepingTime.Ladder.pay_energy
#print axioms KeepingTime.Ladder.pay_pay
#print axioms KeepingTime.Ladder.pay_level
#print axioms KeepingTime.Ladder.sine_rec
#print axioms KeepingTime.Ladder.shift_sum
#print axioms KeepingTime.Ladder.sine_shift
#print axioms KeepingTime.Ladder.two_sub_two_cos_le
#print axioms KeepingTime.Ladder.choice_of_N
#print axioms KeepingTime.Ladder.range_of_ladder
#print axioms KeepingTime.Ladder.choice_of_N_diag
#print axioms KeepingTime.Ladder.N_ge_k
#print axioms KeepingTime.Ladder.range_of_ladder_diag
