import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Constant chains of *The price of keeping time*

* `capital_chain`: Proposition "What the clock costs" (a) for the Hadamard gate. With
  `m = ⌊1/(8(ε+η))⌋` reused blocks the tester error is `δ = mε + (m-1)η ≤ 1/8`, and
  `K E (1/2 - 2δ)^2` with `K = mn` is at least `nE/(256(ε+η))`.
* `capital_scalar`: the scalar step of the capital lemma, `d(p‖r) ≥ p b - ln 2` whenever
  `r ≤ e^{-b}`.
* `hoeffding_exponent`: the exponent of Proposition "The clock's energy is a lottery".
* `converse_b_constant`, `converse_commuting_constant`, `converse_c_chain`, `converse_c_ratio`,
  `converse_c_tau`: the constants 51, 36, `2^17` and `1/12` of Proposition "Strong converse with a
  reusable controller".
* `clocksize_b_chain`, `clocksize_b_final`: the chain of Proposition "How large the clock must be" (b),
  ending in `9βλ/(1024√2) √(n/ζ)`.
* `clocksize_d_chain`, `clocksize_d_f`, `clocksize_d_final`: the chain of (d), ending in
  `βEn/(512√ε)` for `n ≥ 4096`, `ε ≤ 1/4096`.
* `noise_xstar`: the choice of `x_*` in Appendix "Finite horizons" gives `f_0(x_*) ≤ c/2`.
-/

namespace KeepingTime

open Real

/-- A natural floor of a number at least `2` keeps at least half of it. -/
lemma natFloor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : x - 1 < ⌊x⌋₊ := Nat.sub_one_lt_floor x
  linarith

theorem capital_chain (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hpos : 0 < ε + η) (h : ε + η ≤ 1 / 16) :
    1 ≤ ⌊1 / (8 * (ε + η))⌋₊ ∧
      (⌊1 / (8 * (ε + η))⌋₊ : ℝ) * ε + ((⌊1 / (8 * (ε + η))⌋₊ : ℝ) - 1) * η ≤ 1 / 8 ∧
      1 / (256 * (ε + η)) ≤ (⌊1 / (8 * (ε + η))⌋₊ : ℝ) *
        (1 / 2 - 2 * ((⌊1 / (8 * (ε + η))⌋₊ : ℝ) * ε + ((⌊1 / (8 * (ε + η))⌋₊ : ℝ) - 1) * η)) ^ 2 := by
  set ζ := ε + η with hζ
  set m := ⌊1 / (8 * ζ)⌋₊ with hm
  have h8 : 0 < 8 * ζ := by positivity
  have hx : 2 ≤ 1 / (8 * ζ) := by
    rw [le_div_iff₀ h8]; nlinarith
  have hm_ge : 1 / (8 * ζ) / 2 ≤ (m : ℝ) := natFloor_ge_half hx
  have hm_le : (m : ℝ) ≤ 1 / (8 * ζ) := Nat.floor_le (by positivity)
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hmζ : (m : ℝ) * ζ ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_right hm_le hpos.le
    have e : 1 / (8 * ζ) * ζ = 1 / 8 := by field_simp
    linarith
  have hδ0 : 0 ≤ (m : ℝ) * ε + ((m : ℝ) - 1) * η := by nlinarith
  have hδ : (m : ℝ) * ε + ((m : ℝ) - 1) * η ≤ 1 / 8 := by nlinarith
  refine ⟨by exact_mod_cast hm1, hδ, ?_⟩
  have hsq : 1 / 16 ≤ (1 / 2 - 2 * ((m : ℝ) * ε + ((m : ℝ) - 1) * η)) ^ 2 := by nlinarith
  have hm16 : 1 / (16 * ζ) ≤ (m : ℝ) := by
    have : 1 / (8 * ζ) / 2 = 1 / (16 * ζ) := by field_simp; ring
    linarith
  calc 1 / (256 * ζ) = 1 / (16 * ζ) * (1 / 16) := by field_simp; ring
    _ ≤ (m : ℝ) * (1 / 16) := by gcongr
    _ ≤ (m : ℝ) * (1 / 2 - 2 * ((m : ℝ) * ε + ((m : ℝ) - 1) * η)) ^ 2 := by gcongr

/-- The scalar step of the capital lemma: a two-outcome measurement with probabilities `p` on the
controller and `r ≤ e^{-b}` on its Gibbs state gives a binary relative entropy at least `pb - ln 2`. -/
theorem capital_scalar (p r b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hb : r ≤ exp (-b)) :
    p * b - log 2 ≤ p * log (p / r) + (1 - p) * log ((1 - p) / (1 - r)) := by
  have hlogr : log r ≤ -b := by
    calc log r ≤ log (exp (-b)) := log_le_log hr0 hb
      _ = -b := log_exp _
  have hlog1r : log (1 - r) ≤ 0 := log_nonpos (by linarith) (by linarith)
  have hA : p * log p + p * b ≤ p * log (p / r) := by
    rcases hp0.lt_or_eq with hp | hp
    · rw [log_div hp.ne' hr0.ne']; nlinarith
    · rw [← hp]; simp
  have hB : (1 - p) * log (1 - p) ≤ (1 - p) * log ((1 - p) / (1 - r)) := by
    rcases (sub_nonneg.mpr hp1).lt_or_eq with hq | hq
    · rw [log_div hq.ne' (by linarith : (1 - r) ≠ 0)]; nlinarith
    · simp [← hq]
  have hH : binEntropy p ≤ log 2 := binEntropy_le_log_two
  have hHdef : binEntropy p = -(p * log p) - (1 - p) * log (1 - p) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]; ring
  nlinarith

theorem hoeffding_exponent (n g a s : ℝ) (hn : 0 < n) (hs : 0 < s) :
    2 * (n * (g - 2 * a) / 2) ^ 2 / (n * s ^ 2) = n * (g - 2 * a) ^ 2 / (2 * s ^ 2) := by
  field_simp

/-- `8 · 4√2 · √(5/4) ≤ 51`: the constant of part (b). -/
theorem converse_b_constant : 32 * Real.sqrt 2 * Real.sqrt (5 / 4) ≤ 51 := by
  have h : Real.sqrt 2 * Real.sqrt (5 / 4) = Real.sqrt (5 / 2) := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : Real.sqrt (5 / 2) ≤ 51 / 32 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 / 2 by norm_num), Real.sqrt_nonneg (5 / 2)]
  calc 32 * Real.sqrt 2 * Real.sqrt (5 / 4) = 32 * Real.sqrt (5 / 2) := by rw [mul_assoc, h]
    _ ≤ 51 := by linarith

/-- `8 · 4 · √(5/4) ≤ 36`: the constant of part (c) for a controller commuting with its
Hamiltonian. -/
theorem converse_commuting_constant : 32 * Real.sqrt (5 / 4) ≤ 36 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 / 4 by norm_num), Real.sqrt_nonneg (5 / 4)]

/-- Part (c): for `η ≤ 2^{-14}` and `m = ⌊1/(8192η)⌋`, `m ≥ 1`, `2mη ≤ 1/4096` and
`16/(3m) ≤ 2^{17} η`. -/
theorem converse_c_chain (η : ℝ) (hη : 0 < η) (h : η ≤ 1 / 16384) :
    1 ≤ ⌊1 / (8192 * η)⌋₊ ∧ 2 * (⌊1 / (8192 * η)⌋₊ : ℝ) * η ≤ 1 / 4096 ∧
      16 / (3 * (⌊1 / (8192 * η)⌋₊ : ℝ)) ≤ 2 ^ 17 * η := by
  set m := ⌊1 / (8192 * η)⌋₊ with hm
  have hpos : 0 < 8192 * η := by positivity
  have hx : 2 ≤ 1 / (8192 * η) := by rw [le_div_iff₀ hpos]; nlinarith
  have hm_ge : 1 / (8192 * η) / 2 ≤ (m : ℝ) := natFloor_ge_half hx
  have hm_le : (m : ℝ) ≤ 1 / (8192 * η) := Nat.floor_le (by positivity)
  have hm1 : (1 : ℝ) ≤ m := by linarith
  refine ⟨by exact_mod_cast hm1, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hm_le hη.le
    have e : 1 / (8192 * η) * η = 1 / 8192 := by field_simp
    nlinarith
  · have hm' : 1 / (16384 * η) ≤ (m : ℝ) := by
      have : 1 / (8192 * η) / 2 = 1 / (16384 * η) := by field_simp; ring
      linarith
    have hmpos : (0 : ℝ) < m := by linarith
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hm' (by positivity : (0:ℝ) ≤ 2 ^ 17 * η * 3)
    have e : 2 ^ 17 * η * 3 * (1 / (16384 * η)) = 24 := by field_simp; norm_num
    nlinarith

/-- Part (c): `|r^m - 1| ≤ (16/3)√(2mη)` follows from `4√(2mη)√(5/4)` divided by `15/16`. -/
theorem converse_c_ratio : 4 * Real.sqrt (5 / 4) * (16 / 15) ≤ 16 / 3 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 / 4 by norm_num), Real.sqrt_nonneg (5 / 4)]

/-- Part (c): `2mη ≤ 1/4096` gives `τ = (16/3)√(2mη) ≤ 1/12`. -/
theorem converse_c_tau (u : ℝ) (hu : u ≤ 1 / 4096) : 16 / 3 * Real.sqrt u ≤ 1 / 12 := by
  have : Real.sqrt u ≤ 1 / 64 := by
    rw [show (1:ℝ) / 64 = Real.sqrt ((1 / 64) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- Proposition "How large the clock must be" (b): `k = ⌊1/(16ζ)⌋ ≥ 1/(32ζ)` and `kζ ≤ 1/16`. -/
theorem clocksize_b_chain (ζ : ℝ) (hζ : 0 < ζ) (h : ζ ≤ 1 / 32) :
    1 / (32 * ζ) ≤ (⌊1 / (16 * ζ)⌋₊ : ℝ) ∧ (⌊1 / (16 * ζ)⌋₊ : ℝ) * ζ ≤ 1 / 16 := by
  have hpos : 0 < 16 * ζ := by positivity
  have hx : 2 ≤ 1 / (16 * ζ) := by rw [le_div_iff₀ hpos]; nlinarith
  have hk_ge := natFloor_ge_half hx
  have hk_le : (⌊1 / (16 * ζ)⌋₊ : ℝ) ≤ 1 / (16 * ζ) := Nat.floor_le (by positivity)
  constructor
  · have : 1 / (16 * ζ) / 2 = 1 / (32 * ζ) := by field_simp; ring
    linarith
  · have := mul_le_mul_of_nonneg_right hk_le hζ.le
    have e : 1 / (16 * ζ) * ζ = 1 / 16 := by field_simp
    linarith

/-- Proposition "How large the clock must be" (b), last step: from
`3/4 ≤ √(2 v s/(β √(kn)))` with `v = 8/λ` and `k ≥ 1/(32ζ)` follows
`s ≥ 9βλ/(1024√2) · √(n/ζ)`. -/
theorem clocksize_b_final (β lam n ζ k s : ℝ) (hβ : 0 < β) (hl : 0 < lam) (hn : 0 < n) (hζ : 0 < ζ)
    (hk : 1 / (32 * ζ) ≤ k) (hrot : (3 / 4 : ℝ) ≤ Real.sqrt (2 * (8 / lam) * s / (β * Real.sqrt (k * n)))) :
    9 * β * lam / (1024 * Real.sqrt 2) * Real.sqrt (n / ζ) ≤ s := by
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hkn : 0 < Real.sqrt (k * n) := Real.sqrt_pos.mpr (by positivity)
  have hsq : (3 / 4 : ℝ) ^ 2 ≤ 2 * (8 / lam) * s / (β * Real.sqrt (k * n)) := by
    have h0 : (0:ℝ) ≤ 3 / 4 := by norm_num
    have := mul_self_le_mul_self h0 hrot
    rwa [← sq, ← sq, Real.sq_sqrt] at this
    by_contra hneg
    have : Real.sqrt (2 * (8 / lam) * s / (β * Real.sqrt (k * n))) = 0 :=
      Real.sqrt_eq_zero'.mpr (not_le.mp hneg).le
    linarith
  have hs1 : 9 * β * lam * Real.sqrt (k * n) / 256 ≤ s := by
    rw [le_div_iff₀ (by positivity)] at hsq
    field_simp at hsq ⊢
    nlinarith
  have hroot : Real.sqrt (n / ζ) / (4 * Real.sqrt 2) ≤ Real.sqrt (k * n) := by
    have h32 : Real.sqrt (n / (32 * ζ)) = Real.sqrt (n / ζ) / (4 * Real.sqrt 2) := by
      rw [show n / (32 * ζ) = (n / ζ) / 32 by field_simp, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 32)]
      congr 1
      rw [show (32:ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [← h32]
    apply Real.sqrt_le_sqrt
    calc n / (32 * ζ) = 1 / (32 * ζ) * n := by ring
      _ ≤ k * n := by gcongr
  have h2 : 0 < Real.sqrt 2 := by positivity
  calc 9 * β * lam / (1024 * Real.sqrt 2) * Real.sqrt (n / ζ)
      = 9 * β * lam * (Real.sqrt (n / ζ) / (4 * Real.sqrt 2)) / 256 := by field_simp; ring
    _ ≤ 9 * β * lam * Real.sqrt (k * n) / 256 := by gcongr
    _ ≤ s := hs1

/-- Proposition "How large the clock must be" (d): for `n ≥ 4096`, `0 < ε ≤ 1/4096` and
`t = 64√ε/(nE)`, the dephasing term `nE²t²/4` is at most `ε/4`, the angle `φ = 64√ε` is at most `1`,
and `2√ε + 2√(2ε) < 8√ε`. -/
theorem clocksize_d_chain (ε n E : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4096) (hn : 4096 ≤ n) (hE : 0 < E) :
    n * E ^ 2 * (64 * Real.sqrt ε / (n * E)) ^ 2 / 4 ≤ ε / 4 ∧ 64 * Real.sqrt ε ≤ 1 ∧
      2 * Real.sqrt ε + 2 * Real.sqrt (2 * ε) < 8 * Real.sqrt ε := by
  have hn0 : 0 < n := by linarith
  have hsε : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hspos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  refine ⟨?_, ?_, ?_⟩
  · have e : n * E ^ 2 * (64 * Real.sqrt ε / (n * E)) ^ 2 / 4 = 1024 * ε / n := by
      field_simp; rw [hsε]; ring
    rw [e, div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  · nlinarith [Real.sqrt_nonneg ε]
  · rw [Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 2 < 3 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    nlinarith

/-- Proposition "How large the clock must be" (d): `f sin(32√ε) ≤ 8√ε` with `ε ≤ 1/4096` forces
`f ≤ π/8`, hence `1 - f > 1/2`. -/
theorem clocksize_d_f (ε f : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4096) (hf : 0 ≤ f)
    (h : f * Real.sin (32 * Real.sqrt ε) ≤ 8 * Real.sqrt ε) : f ≤ π / 8 ∧ 1 / 2 < 1 - f := by
  have hspos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs : Real.sqrt ε ≤ 1 / 64 := by
    rw [show (1:ℝ) / 64 = Real.sqrt ((1 / 64) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  set x := 32 * Real.sqrt ε with hx
  have hx0 : 0 ≤ x := by positivity
  have hxπ : x ≤ π / 2 := by have := Real.pi_gt_three; linarith
  have hjordan : 2 / π * x ≤ Real.sin x := Real.mul_le_sin hx0 hxπ
  have hπ : 0 < π := Real.pi_pos
  have key : f * (2 / π * x) ≤ x / 4 := by
    calc f * (2 / π * x) ≤ f * Real.sin x := by gcongr
      _ ≤ 8 * Real.sqrt ε := h
      _ = x / 4 := by rw [hx]; ring
  have hxpos : 0 < x := by positivity
  have hfle : f ≤ π / 8 := by
    have : f * (2 / π) ≤ 1 / 4 := by
      have := key
      rw [show f * (2 / π * x) = f * (2 / π) * x by ring, show x / 4 = 1 / 4 * x by ring] at this
      exact le_of_mul_le_mul_right this hxpos
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hπ] at this
    linarith
  exact ⟨hfle, by have := Real.pi_lt_four; linarith⟩

/-- Proposition "How large the clock must be" (d), last step: `1/4 < 2ts/β` gives `s > β/(8t)`,
and with `t = 64√ε/(nE)` this is `βEn/(512√ε)`. -/
theorem clocksize_d_final (β t s : ℝ) (hβ : 0 < β) (ht : 0 < t) (h : 1 / 4 < 2 * t * s / β) :
    β / (8 * t) < s := by
  rw [lt_div_iff₀ hβ] at h
  rw [div_lt_iff₀ (by positivity)]
  linarith

theorem clocksize_d_value (β ε n E : ℝ) (hε : 0 < ε) (hn : 0 < n) (hE : 0 < E) :
    β / (8 * (64 * Real.sqrt ε / (n * E))) = β * E * n / (512 * Real.sqrt ε) := by
  have : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  field_simp; ring

/-- Appendix "Finite horizons": `x_* ≤ (c/(64 ℓ))^4` and `x_* ≤ c/(4K)` give
`f_0(x_*) = K x_* + 4 min{1, 4 x_*^{1/4}} ℓ ≤ c/2`, with `ℓ = ln d` and `K = 2βh + ln d`. -/
theorem noise_xstar (c ℓ K x : ℝ) (hc : 0 < c) (hℓ : 0 < ℓ) (hK : 0 < K) (hx : 0 ≤ x)
    (h1 : x ≤ (c / (64 * ℓ)) ^ 4) (h2 : x ≤ c / (4 * K)) :
    K * x + 4 * min 1 (4 * x ^ ((1:ℝ) / 4)) * ℓ ≤ c / 2 := by
  have hq : x ^ ((1:ℝ) / 4) ≤ c / (64 * ℓ) := by
    have hy : 0 ≤ c / (64 * ℓ) := by positivity
    calc x ^ ((1:ℝ) / 4) ≤ ((c / (64 * ℓ)) ^ 4) ^ ((1:ℝ) / 4) :=
          Real.rpow_le_rpow hx h1 (by norm_num)
      _ = c / (64 * ℓ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  have hmin : min 1 (4 * x ^ ((1:ℝ) / 4)) ≤ c / (16 * ℓ) := by
    calc min 1 (4 * x ^ ((1:ℝ) / 4)) ≤ 4 * x ^ ((1:ℝ) / 4) := min_le_right _ _
      _ ≤ 4 * (c / (64 * ℓ)) := by gcongr
      _ = c / (16 * ℓ) := by field_simp; ring
  have hKx : K * x ≤ c / 4 := by
    calc K * x ≤ K * (c / (4 * K)) := by gcongr
      _ = c / 4 := by field_simp
  have h4 : 4 * min 1 (4 * x ^ ((1:ℝ) / 4)) * ℓ ≤ c / 4 := by
    calc 4 * min 1 (4 * x ^ ((1:ℝ) / 4)) * ℓ ≤ 4 * (c / (16 * ℓ)) * ℓ := by gcongr
      _ = c / 4 := by field_simp; ring
  linarith

end KeepingTime

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms KeepingTime.capital_chain
#print axioms KeepingTime.capital_scalar
#print axioms KeepingTime.hoeffding_exponent
#print axioms KeepingTime.converse_b_constant
#print axioms KeepingTime.converse_commuting_constant
#print axioms KeepingTime.converse_c_chain
#print axioms KeepingTime.converse_c_ratio
#print axioms KeepingTime.converse_c_tau
#print axioms KeepingTime.clocksize_b_chain
#print axioms KeepingTime.clocksize_b_final
#print axioms KeepingTime.clocksize_d_chain
#print axioms KeepingTime.clocksize_d_f
#print axioms KeepingTime.clocksize_d_final
#print axioms KeepingTime.clocksize_d_value
#print axioms KeepingTime.noise_xstar
