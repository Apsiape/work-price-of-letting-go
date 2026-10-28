import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic

/-!
# The strong converse: finite and arithmetic cores (Section 4 and Appendix C)

* `degenerate_target`: a battery projector of rank `R_B` whose energies are all at least `E_init - W` has
  `b_β(P_B) ≤ β W/ln2 + log2 R_B` (Section 4, after Theorem "Strong converse");
* `ic_count`: in an energy block of dimension `m` the vectors `e_i`, `e_i + e_k`, `e_i + i e_k` (`i < k`) number
  `m + 2·C(m,2) = m²` (Appendix C.2); `sum_sq_le_sq_sum`: over all blocks `L = Σ m_b² ≤ (Σ m_b)² = d⁴`;
* `rejected_weight`, `cap_constant`: the arithmetic of Lemma "cap" (C.4) (`a₀ Z_K = (1-s)/2`, and `2 log2(2/(1-s)) = 4` at
  `s = 1/2`);
* `purified_quarter`, `eat_bracket`: the two estimates of C.5 (`4δ/r ≤ 1/16`; `1 - 2 log2(δ p_G) ≤ 13 + 4 log2(1/p)`);
* `assembly`: combining (eq. eat) and (eq. cap) gives the displayed inequality of C.5;
* `final_gap`: with `a = min{δ/16, δ²/(256 C_f²)}` and `log2(1/p) ≤ aN`, the right-hand side exceeds `N(K - δ)` as soon
  as `C_f √(13N) ≤ Nδ/8` and `4 < Nδ/8`.
-/

open Real

namespace Converse

theorem degenerate_target (β Einit W : ℝ) (hβ : 0 ≤ β) {ι : Type*} (S : Finset ι) (E : ι → ℝ)
    (hS : S.Nonempty) (hE : ∀ i ∈ S, Einit - W ≤ E i) :
    β * Einit / log 2 + logb 2 (∑ i ∈ S, exp (-(β * E i))) ≤ β * W / log 2 + logb 2 (S.card) := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hpos : 0 < ∑ i ∈ S, exp (-(β * E i)) := Finset.sum_pos (fun i _ => exp_pos _) hS
  have hle : ∑ i ∈ S, exp (-(β * E i)) ≤ S.card * exp (-(β * (Einit - W))) := by
    have : ∀ i ∈ S, exp (-(β * E i)) ≤ exp (-(β * (Einit - W))) := by
      intro i hi
      apply exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (hE i hi) hβ
      linarith
    calc ∑ i ∈ S, exp (-(β * E i)) ≤ ∑ _i ∈ S, exp (-(β * (Einit - W))) := Finset.sum_le_sum this
      _ = S.card * exp (-(β * (Einit - W))) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hlog : logb 2 (∑ i ∈ S, exp (-(β * E i))) ≤ logb 2 (S.card * exp (-(β * (Einit - W)))) :=
    (logb_le_logb (by norm_num) hpos (by positivity)).mpr hle
  rw [logb_mul hcard.ne' (exp_pos _).ne'] at hlog
  have : logb 2 (exp (-(β * (Einit - W)))) = -(β * (Einit - W)) / log 2 := by
    rw [logb, log_exp]
  rw [this] at hlog
  have e : β * Einit / log 2 + (-(β * (Einit - W)) / log 2) = β * W / log 2 := by
    field_simp; ring
  linarith

theorem ic_count (m : ℕ) : m + 2 * m.choose 2 = m ^ 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (f a * ∑ i ∈ s, f i)]

theorem rejected_weight (a0 ZK s : ℝ) (hZ : 0 < ZK) (ha : a0 = (1 - s) / (2 * ZK)) :
    a0 * ZK = (1 - s) / 2 := by
  rw [ha]; field_simp

theorem cap_constant : 2 * logb 2 (2 / (1 - 1 / 2)) = 4 := by
  have : (2 : ℝ) / (1 - 1 / 2) = 2 ^ (2 : ℕ) := by norm_num
  rw [this, logb_pow, logb_self_eq_one (by norm_num)]
  norm_num

theorem purified_quarter (δ r : ℝ) (hr : 0 < r) (h : δ ≤ r / 64) : 4 * δ / r ≤ 1 / 16 := by
  rw [div_le_iff₀ hr]; linarith

theorem eat_bracket (p pG : ℝ) (hp : 0 < p) (hpG : p ≤ pG) :
    1 - 2 * logb 2 (p / 64 * pG) ≤ 13 + 4 * logb 2 (1 / p) := by
  have hpG0 : 0 < pG := lt_of_lt_of_le hp hpG
  have h64 : logb 2 (64 : ℝ) = 6 := by
    have : (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
    rw [this, logb_pow, logb_self_eq_one (by norm_num)]; norm_num
  rw [logb_mul (by positivity) hpG0.ne', logb_div hp.ne' (by norm_num), h64, one_div, logb_inv]
  have : logb 2 p ≤ logb 2 pG := (logb_le_logb (by norm_num) hp hpG0).mpr hpG
  linarith

lemma sqrt_add_le_add_sqrt' (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rw [sqrt_le_left]
  · nlinarith [sq_sqrt hx, sq_sqrt hy, mul_nonneg (sqrt_nonneg x) (sqrt_nonneg y)]
  · positivity

/-- C.5: combining the entropy-accumulation bound with the cap. `e` stands for `β(ΔE - u)/ln2`, `θ` for
`θ_γ`, `ℓ` for `log2(1/p)` and `X` for `1 - 2 log2(δ p_G)`. -/
theorem assembly (N h e θ C ℓ X Hd Hh b lr : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hEAT : Hd > N * h - C * √(N * X)) (hX : X ≤ 13 + 4 * ℓ) (hproj : Hh ≥ Hd + lr) (hr : lr ≥ -ℓ)
    (hcap : Hh ≤ b - N * e + N * θ + ℓ + 4) :
    b > N * (h + e - θ) - C * √(N * (13 + 4 * ℓ)) - 2 * ℓ - 4 := by
  have hs : √(N * X) ≤ √(N * (13 + 4 * ℓ)) := sqrt_le_sqrt (mul_le_mul_of_nonneg_left hX hN)
  have := mul_le_mul_of_nonneg_left hs hC
  nlinarith

theorem final_gap (δ C N K ℓ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hN : 0 < N) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ min (δ / 16) (δ ^ 2 / (256 * C ^ 2)) * N)
    (hN1 : C * √(13 * N) ≤ N * δ / 8) (hN2 : 4 < N * δ / 8) :
    N * (K - δ / 2) - C * √(N * (13 + 4 * ℓ)) - 2 * ℓ - 4 > N * (K - δ) := by
  set a := min (δ / 16) (δ ^ 2 / (256 * C ^ 2)) with ha
  have ha1 : a ≤ δ / 16 := min_le_left _ _
  have ha2 : a ≤ δ ^ 2 / (256 * C ^ 2) := min_le_right _ _
  have ha0 : 0 ≤ a := le_min (by positivity) (by positivity)
  -- √(N(13 + 4ℓ)) ≤ √(13N) + 2N√a
  have hsplit : √(N * (13 + 4 * ℓ)) ≤ √(13 * N) + √(4 * N * ℓ) := by
    have : N * (13 + 4 * ℓ) = 13 * N + 4 * N * ℓ := by ring
    rw [this]; exact sqrt_add_le_add_sqrt' _ _ (by positivity) (by positivity)
  have h4 : √(4 * N * ℓ) ≤ 2 * N * √a := by
    have : 4 * N * ℓ ≤ (2 * N * √a) ^ 2 := by
      rw [mul_pow, mul_pow, sq_sqrt ha0]; nlinarith
    calc √(4 * N * ℓ) ≤ √((2 * N * √a) ^ 2) := sqrt_le_sqrt this
      _ = 2 * N * √a := sqrt_sq (by positivity)
  have hsa : C * √a ≤ δ / 16 := by
    have : √a ≤ √(δ ^ 2 / (256 * C ^ 2)) := sqrt_le_sqrt ha2
    have e : √(δ ^ 2 / (256 * C ^ 2)) = δ / (16 * C) := by
      rw [show δ ^ 2 / (256 * C ^ 2) = (δ / (16 * C)) ^ 2 by field_simp; ring]
      exact sqrt_sq (by positivity)
    rw [e] at this
    calc C * √a ≤ C * (δ / (16 * C)) := mul_le_mul_of_nonneg_left this hC.le
      _ = δ / 16 := by field_simp
  have hl : 2 * ℓ ≤ N * δ / 8 := by nlinarith
  have hroot : C * √(N * (13 + 4 * ℓ)) ≤ C * √(13 * N) + C * (2 * N * √a) := by
    have h5 : √(N * (13 + 4 * ℓ)) ≤ √(13 * N) + 2 * N * √a := by linarith
    have := mul_le_mul_of_nonneg_left h5 hC.le
    linarith
  have h2 : C * (2 * N * √a) ≤ N * δ / 8 := by nlinarith
  nlinarith

end Converse

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Converse.degenerate_target
#print axioms Converse.ic_count
#print axioms Converse.sum_sq_le_sq_sum
#print axioms Converse.rejected_weight
#print axioms Converse.cap_constant
#print axioms Converse.purified_quarter
#print axioms Converse.eat_bracket
#print axioms Converse.sqrt_add_le_add_sqrt'
#print axioms Converse.assembly
#print axioms Converse.final_gap
