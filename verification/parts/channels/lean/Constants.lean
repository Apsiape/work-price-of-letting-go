import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Constant chains of the construction and the fixed-error converse (Appendices A and B)

* `formation_dim`, `formation_weight`: the reservoir with levels `j W_f` and integer degeneracies
  `m^j K^{L-j}` has equal Gibbs weight `K^L` on every level when `e^{-β W_f} = K/m`, and the swapped
  subspaces `C ⊗ |1⟩ ⊗ R_j` and `ran Π ⊗ |0⟩ ⊗ R_{j+1}` have equal dimension (`m · m^j K^{L-j} =
  K · m^{j+1} K^{L-j-1}`);
* `converter_ratio`: if `θ ≤ (1 - e^{-βs})/2` and `s > 0` then `(1 - θ) e^{βs} > 1`;
* `postproj`: for `0 < r ≤ 1` and `0 ≤ δ ≤ r/64`, the squared purified distance
  `1 - ((√r - √2 δ)/√(r+δ))²` is at most `4δ/r ≤ 1/16`;
* `assembly`: with `a = min{δ'/16, δ'²/(256 C²)}`,
  `C √(n(13 + 4an)) + 2an ≤ C √(13 n) + n δ'/4`, the step that makes the right side of the
  assembled inequality exceed `n(T - δ')` for large `n`;
* `assembly_log`: `1 - 2 log₂(δ p) = 13 + 4 log₂(1/p)` at `δ = p/64`.
-/

namespace Constants

open Real

theorem formation_dim (m K L j : ℕ) (hj : j < L) :
    m * (m ^ j * K ^ (L - j)) = K * (m ^ (j + 1) * K ^ (L - (j + 1))) := by
  have : L - j = (L - (j + 1)) + 1 := by omega
  rw [this, pow_succ, pow_succ]
  ring

theorem formation_weight (m K : ℝ) (hm : m ≠ 0) (L j : ℕ) (hj : j ≤ L) :
    m ^ j * K ^ (L - j) * (K / m) ^ j = K ^ L := by
  rw [div_pow, mul_div_assoc', mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  field_simp

theorem converter_ratio {s θ : ℝ} (hs : 0 < s) (hθ : θ ≤ (1 - exp (-s)) / 2) :
    1 < (1 - θ) * exp s := by
  have he : 1 < exp s := Real.one_lt_exp_iff.mpr hs
  have hn : exp (-s) * exp s = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < exp s := exp_pos s
  nlinarith

theorem postproj {r δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hδr : δ ≤ r / 64) :
    1 - ((√r - √2 * δ) / √(r + δ)) ^ 2 ≤ 4 * δ / r ∧ 4 * δ / r ≤ 1 / 16 := by
  have hsr : √r ^ 2 = r := Real.sq_sqrt hr.le
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrd : 0 < r + δ := by linarith
  have hsrd : √(r + δ) ^ 2 = r + δ := Real.sq_sqrt hrd.le
  have hpos : 0 < √(r + δ) := Real.sqrt_pos.mpr hrd
  have h8 : √2 * √r ≤ 3 / 2 := by
    rw [← Real.sqrt_mul (by norm_num) r, Real.sqrt_le_left (by norm_num)]
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [div_pow, hsrd]
    have key : (r + δ - (√r - √2 * δ) ^ 2) * r ≤ 4 * δ * (r + δ) := by
      have e : (√r - √2 * δ) ^ 2 = r - 2 * δ * (√2 * √r) + 2 * δ ^ 2 := by nlinarith
      rw [e]
      have h9 := mul_le_mul_of_nonneg_left h8 (mul_nonneg hδ hr.le)
      nlinarith [mul_nonneg (mul_nonneg hδ hδ) hr.le]
    have e2 : 1 - (√r - √2 * δ) ^ 2 / (r + δ) = (r + δ - (√r - √2 * δ) ^ 2) / (r + δ) := by
      field_simp
    rw [e2, div_le_div_iff₀ hrd hr]
    linarith
  · rw [div_le_iff₀ hr]
    linarith

theorem assembly {C δ' n : ℝ} (hC : 0 < C) (hδ : 0 < δ') (hn : 0 ≤ n) :
    C * √(n * (13 + 4 * min (δ' / 16) (δ' ^ 2 / (256 * C ^ 2)) * n))
        + 2 * min (δ' / 16) (δ' ^ 2 / (256 * C ^ 2)) * n
      ≤ C * √(13 * n) + n * δ' / 4 := by
  set a := min (δ' / 16) (δ' ^ 2 / (256 * C ^ 2))
  have ha0 : 0 ≤ a := le_min (by positivity) (by positivity)
  have ha1 : a ≤ δ' / 16 := min_le_left _ _
  have ha2 : a ≤ δ' ^ 2 / (256 * C ^ 2) := min_le_right _ _
  -- √(13n + 4a n²) ≤ √(13n) + n √(4a)
  have hsplit : √(n * (13 + 4 * a * n)) ≤ √(13 * n) + n * √(4 * a) := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : √(13 * n) ^ 2 = 13 * n := Real.sq_sqrt (by positivity)
    have h2 : √(4 * a) ^ 2 = 4 * a := Real.sq_sqrt (by positivity)
    have hu := Real.sqrt_nonneg (13 * n)
    have hv := mul_nonneg hn (Real.sqrt_nonneg (4 * a))
    calc n * (13 + 4 * a * n) = √(13 * n) ^ 2 + (n * √(4 * a)) ^ 2 := by rw [mul_pow, h1, h2]; ring
      _ ≤ (√(13 * n) + n * √(4 * a)) ^ 2 := by nlinarith [mul_nonneg hu hv]
  -- C √(4a) ≤ δ'/8
  have hroot : C * √(4 * a) ≤ δ' / 8 := by
    have h4 : 4 * a ≤ (δ' / (8 * C)) ^ 2 := by
      rw [div_pow, mul_pow]
      rw [le_div_iff₀ (by positivity)]
      have : a * (256 * C ^ 2) ≤ δ' ^ 2 := by rwa [le_div_iff₀ (by positivity)] at ha2
      nlinarith
    have : √(4 * a) ≤ δ' / (8 * C) := by
      rw [Real.sqrt_le_left (by positivity)]
      exact h4
    calc C * √(4 * a) ≤ C * (δ' / (8 * C)) := mul_le_mul_of_nonneg_left this hC.le
      _ = δ' / 8 := by field_simp
  have hlin : 2 * a * n ≤ n * δ' / 8 := by nlinarith
  calc C * √(n * (13 + 4 * a * n)) + 2 * a * n
      ≤ C * (√(13 * n) + n * √(4 * a)) + 2 * a * n := by
        have := mul_le_mul_of_nonneg_left hsplit hC.le
        linarith
    _ = C * √(13 * n) + n * (C * √(4 * a)) + 2 * a * n := by ring
    _ ≤ C * √(13 * n) + n * (δ' / 8) + n * δ' / 8 := by
        have := mul_le_mul_of_nonneg_left hroot hn
        linarith
    _ = C * √(13 * n) + n * δ' / 4 := by ring

theorem assembly_log {p : ℝ} (hp : 0 < p) :
    1 - 2 * Real.logb 2 (p / 64 * p) = 13 + 4 * Real.logb 2 (1 / p) := by
  have h64 : Real.logb 2 64 = 6 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_mul (by positivity) hp.ne', Real.logb_div hp.ne' (by norm_num), h64,
    Real.logb_div one_ne_zero hp.ne', Real.logb_one]
  ring

end Constants

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Constants.formation_dim
#print axioms Constants.formation_weight
#print axioms Constants.converter_ratio
#print axioms Constants.postproj
#print axioms Constants.assembly
#print axioms Constants.assembly_log
