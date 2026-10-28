import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The compiler without time covariance: constant chains of Appendix E

* `e9_trace_bound`: from `w ≤ g' + a_s - F`, `J(Z₀) + F ≥ -C₀` and `g' ≤ C₀`, `d[w - J(Z₀)] ≤ d(2C₀ + a_s)` (E9),
  and `e10_norm_bound`: `c d (2C₀ + a_s)/δ` bounds the effect norm (E10);
* `rate_chain`: `a_m - F ≤ η`, `F + w ≤ g' + a_s` and `g' ≤ g + δ C₀` give `a_m + w ≤ g + δ C₀ + a_s + η` (E27);
* `debit_sum`: the four factory debits sum to `m F_τ + (r - k + mσ) ln2/β + 2 s₀` (E14), and `debit_remainder`:
  with `k = ⌈m(σ + 2γ)⌉`, `r = ⌈3mγ⌉ + 4`, the remainder `r - k + mσ` lies in `[mγ + 3, mγ + 5]`;
* `fiber_fits`: a typical string has `k + log2 p_x ≤ r`, so its `⌊K p_x⌋` labels fit in the residue, and
  `typical_fraction`: `#typical/K ≤ 2^{-mγ}` (E13);
* `cache_average`, `clock_average`, `cache_capital`: `(1/m) Σ_{k<m} k = (m-1)/2`, the same for `m-1-k`, and the
  capital formula (E20) given additivity of relative entropy over the cache cells;
* `boundary_count`: exactly `N` initial clock values meet a boundary in `N ≤ m` calls (`p = N/m`), and
  `clock_charge`: the clock releases `(m-1) a_m` and, with the main debit `a_m`, charges `m a_m`.
-/

open Real

namespace Factory

theorem e9_trace_bound (d w g' a_s F J0 C0 : ℝ) (hd : 0 ≤ d) (h8 : F + w ≤ g' + a_s) (hJ : J0 + F ≥ -C0)
    (hg : g' ≤ C0) : d * (w - J0) ≤ d * (2 * C0 + a_s) := by
  apply mul_le_mul_of_nonneg_left _ hd
  linarith

theorem e10_norm_bound (c d C0 a_s δ trD : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ) (htr : trD ≤ d * (2 * C0 + a_s)) :
    c / δ * trD ≤ c * d * (2 * C0 + a_s) / δ := by
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ, mul_assoc]
  exact mul_le_mul_of_nonneg_left htr hc

theorem rate_chain (a_m F w g' g a_s δ C0 η : ℝ) (hfac : a_m - F ≤ η) (h8 : F + w ≤ g' + a_s)
    (h6 : g' ≤ g + δ * C0) : a_m + w ≤ g + δ * C0 + a_s + η := by
  linarith

theorem debit_sum (m β s0 hmin lnZ trT σ R : ℝ) (r k : ℕ) (hβ : 0 < β) (hR : 0 < R) (mn : ℕ) (hm : (mn : ℝ) = m) :
    (m * (hmin + lnZ / β) + s0) + (log (R ^ mn * 2 ^ r) - log (2 ^ k)) / β + m * (trT - hmin)
      - (m * log R / β - s0)
      = m * (trT + lnZ / β - σ * log 2 / β) + ((r : ℝ) - k + m * σ) * log 2 / β + 2 * s0 := by
  rw [log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, hm]
  field_simp
  ring

theorem debit_remainder (m γ σ : ℝ) :
    m * γ + 3 ≤ ((⌈3 * m * γ⌉ + 4 : ℤ) : ℝ) - (⌈m * (σ + 2 * γ)⌉ : ℝ) + m * σ ∧
      ((⌈3 * m * γ⌉ + 4 : ℤ) : ℝ) - (⌈m * (σ + 2 * γ)⌉ : ℝ) + m * σ ≤ m * γ + 5 := by
  have a1 := Int.le_ceil (3 * m * γ)
  have a2 := Int.ceil_lt_add_one (3 * m * γ)
  have b1 := Int.le_ceil (m * (σ + 2 * γ))
  have b2 := Int.ceil_lt_add_one (m * (σ + 2 * γ))
  push_cast
  constructor <;> nlinarith

theorem fiber_fits (m γ σ lp : ℝ) (hlp : lp ≤ -(m * (σ - γ))) :
    (⌈m * (σ + 2 * γ)⌉ : ℝ) + lp ≤ ((⌈3 * m * γ⌉ + 4 : ℤ) : ℝ) := by
  have a1 := Int.le_ceil (3 * m * γ)
  have b2 := Int.ceil_lt_add_one (m * (σ + 2 * γ))
  push_cast
  nlinarith

theorem fiber_fits_rpow (m γ σ lp : ℝ) (hlp : lp ≤ -(m * (σ - γ))) :
    (2 : ℝ) ^ ((⌈m * (σ + 2 * γ)⌉ : ℝ) + lp) ≤ (2 : ℝ) ^ (((⌈3 * m * γ⌉ + 4 : ℤ) : ℝ)) :=
  rpow_le_rpow_of_exponent_le (by norm_num) (fiber_fits m γ σ lp hlp)

theorem typical_fraction (m γ σ ntyp : ℝ) (hn : ntyp ≤ (2 : ℝ) ^ (m * (σ + γ))) :
    ntyp / (2 : ℝ) ^ ((⌈m * (σ + 2 * γ)⌉ : ℝ)) ≤ (2 : ℝ) ^ (-(m * γ)) := by
  have hK : (2 : ℝ) ^ (m * (σ + 2 * γ)) ≤ (2 : ℝ) ^ ((⌈m * (σ + 2 * γ)⌉ : ℝ)) :=
    rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
  have hpos : 0 < (2 : ℝ) ^ (m * (σ + 2 * γ)) := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hK)]
  calc ntyp ≤ (2 : ℝ) ^ (m * (σ + γ)) := hn
    _ = (2 : ℝ) ^ (-(m * γ)) * (2 : ℝ) ^ (m * (σ + 2 * γ)) := by
        rw [← rpow_add (by norm_num)]; congr 1; ring
    _ ≤ (2 : ℝ) ^ (-(m * γ)) * (2 : ℝ) ^ ((⌈m * (σ + 2 * γ)⌉ : ℝ)) :=
        mul_le_mul_of_nonneg_left hK (by positivity)

theorem cache_average (m : ℕ) (hm : 0 < m) :
    (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, (k : ℝ) = ((m : ℝ) - 1) / 2 := by
  have h := Finset.sum_range_id_mul_two m
  have : (∑ k ∈ Finset.range m, (k : ℝ)) * 2 = (m : ℝ) * ((m : ℝ) - 1) := by
    have h' : ((∑ k ∈ Finset.range m, k : ℕ) : ℝ) * 2 = ((m * (m - 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)] at h'
    push_cast at h'
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  linarith

theorem clock_average (m : ℕ) (hm : 0 < m) :
    (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, ((m : ℝ) - 1 - k) = ((m : ℝ) - 1) / 2 := by
  have h := cache_average m hm
  have e : ∑ k ∈ Finset.range m, ((m : ℝ) - 1 - k) = (m : ℝ) * ((m : ℝ) - 1) - ∑ k ∈ Finset.range m, (k : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [e]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mul_sub, h]
  field_simp
  ring

/-- (E20): with `D(τ^{⊗k} ⊗ γ^{⊗(m-1-k)} ‖ γ^{⊗(m-1)}) = k β F_τ` and a uniform clock against `γ_clock`,
the capital `(1/m) Σ_k [k β F_τ + log(1/m) + β (m-1-k) a_m + log Z_clock]` equals
`β ((m-1)/2 (F_τ + a_m)) + log (Z_clock/m)`. -/
theorem cache_capital (m : ℕ) (hm : 0 < m) (β F a Zc : ℝ) (hZ : 0 < Zc) :
    (1 / (m : ℝ)) * ∑ k ∈ Finset.range m, ((k : ℝ) * β * F + log (1 / (m : ℝ)) + β * ((m : ℝ) - 1 - k) * a + log Zc)
      = β * (((m : ℝ) - 1) / 2 * (F + a)) + log (Zc / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hA := cache_average m hm
  have hB := clock_average m hm
  have e : ∑ k ∈ Finset.range m, ((k : ℝ) * β * F + log (1 / (m : ℝ)) + β * ((m : ℝ) - 1 - k) * a + log Zc)
      = β * F * ∑ k ∈ Finset.range m, (k : ℝ) + (m : ℝ) * (log (1 / (m : ℝ)) + log Zc)
        + β * a * ∑ k ∈ Finset.range m, ((m : ℝ) - 1 - k) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    have h1 : ∀ k ∈ Finset.range m, (k : ℝ) * β * F = β * F * k := fun k _ => by ring
    have h2 : ∀ k ∈ Finset.range m, β * ((m : ℝ) - 1 - k) * a = β * a * ((m : ℝ) - 1 - k) := fun k _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    ring
  have hl : log (1 / (m : ℝ)) = -log m := by rw [one_div, log_inv]
  rw [e, hl, log_div hZ.ne' hm'.ne']
  have : (1 / (m : ℝ)) * (β * F * ∑ k ∈ Finset.range m, (k : ℝ) + (m : ℝ) * (-log m + log Zc)
        + β * a * ∑ k ∈ Finset.range m, ((m : ℝ) - 1 - k))
      = β * F * ((1 / (m : ℝ)) * ∑ k ∈ Finset.range m, (k : ℝ)) + (-log m + log Zc)
        + β * a * ((1 / (m : ℝ)) * ∑ k ∈ Finset.range m, ((m : ℝ) - 1 - k)) := by
    field_simp
  rw [this, hA, hB]
  ring

theorem boundary_count (m N : ℕ) (hN : N ≤ m) : ((Finset.range m).filter (fun k => k < N)).card = N := by
  have : (Finset.range m).filter (fun k => k < N) = Finset.range N := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

theorem clock_charge (m : ℕ) (a : ℝ) : ((m : ℝ) - 1) * a + a = m * a := by ring

end Factory

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Factory.e9_trace_bound
#print axioms Factory.e10_norm_bound
#print axioms Factory.rate_chain
#print axioms Factory.debit_sum
#print axioms Factory.debit_remainder
#print axioms Factory.fiber_fits
#print axioms Factory.fiber_fits_rpow
#print axioms Factory.typical_fraction
#print axioms Factory.cache_average
#print axioms Factory.clock_average
#print axioms Factory.cache_capital
#print axioms Factory.boundary_count
#print axioms Factory.clock_charge
