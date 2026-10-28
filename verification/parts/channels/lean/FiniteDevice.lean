import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic

/-!
# The finite amplitude-damping device and the finite saving (Section 4)

**The shell preparation.**  The `k`-excitation shell of the pool (`n` memories and `R`
reservoir qubits) has dimension `C(R+n, k)`; it is moved onto "every memory in its ground state,
reservoir shell `k + w`, battery lowered by `w`" when `C(R, k+w) ≥ C(R+n, k)`.

* `ratio_mono`: the ratio `C(R, k+w)/C(R+n, k)` does not increase in `k`, in cross-multiplied
  form, for all `R, n, k, w`;
* `bad_succ`, `bad_upper`: hence the shells that cannot be moved form an upper tail;
* `shell_embedding`: when the inequality holds, an injective map from the source shell to the
  target shell exists, and it conserves energy (`k` excitations plus the battery's `w` on one
  side, `k + w` reservoir excitations on the other);
* `table_counts`: the qubit counts of Table 1 and the 7-qubit counter.

**The finite saving.**  Integer facts behind the paragraph "A finite saving":
`w = 137` (resp. `150`) is the least integer with `2^w ≥ (3/2)^n` at `n = 234` (resp. `256`);
`r = 5` (resp. `11`) is the largest refund with `8 · 2^r (5/6)^n ≤ (10^{-8} - 10^{-12})^2`; and
the decoding error `10^{-12} + √(8 · 32 (5/6)^234)` is below `8.71 · 10^{-9}`.
-/

namespace FiniteDevice

/-- The ratio `C(R, k+w)/C(R+n, k)` is non-increasing in `k` (cross-multiplied). -/
theorem ratio_mono (R n k w : ℕ) :
    R.choose (k + w + 1) * (R + n).choose k ≤ R.choose (k + w) * (R + n).choose (k + 1) := by
  set j := k + w with hj
  have h1 := Nat.choose_succ_right_eq R j
  have h2 := Nat.choose_succ_right_eq (R + n) k
  set a := R.choose j
  set a' := R.choose (j + 1)
  set b := (R + n).choose k
  set b' := (R + n).choose (k + 1)
  have hpos : 0 < (j + 1) * (k + 1) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  have hm : (R - j) * (k + 1) ≤ (R + n - k) * (j + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a' * b * ((j + 1) * (k + 1)) = (a' * (j + 1)) * b * (k + 1) := by ring
    _ = a * (R - j) * b * (k + 1) := by rw [h1]
    _ = a * b * ((R - j) * (k + 1)) := by ring
    _ ≤ a * b * ((R + n - k) * (j + 1)) := Nat.mul_le_mul_left _ hm
    _ = a * (b * (R + n - k)) * (j + 1) := by ring
    _ = a * (b' * (k + 1)) * (j + 1) := by rw [h2]
    _ = a * b' * ((j + 1) * (k + 1)) := by ring

/-- A shell that cannot be moved is followed by another one (inside the pool). -/
theorem bad_succ {R n k w : ℕ} (hk : k + 1 ≤ R + n)
    (hbad : R.choose (k + w) < (R + n).choose k) :
    R.choose (k + 1 + w) < (R + n).choose (k + 1) := by
  have hm := ratio_mono R n k w
  have hb' : 0 < (R + n).choose (k + 1) := Nat.choose_pos hk
  have hb : 0 < (R + n).choose k := Nat.choose_pos (by omega)
  rw [show k + 1 + w = k + w + 1 by ring]
  have : R.choose (k + w + 1) * (R + n).choose k < (R + n).choose (k + 1) * (R + n).choose k :=
    calc R.choose (k + w + 1) * (R + n).choose k
        ≤ R.choose (k + w) * (R + n).choose (k + 1) := hm
      _ < (R + n).choose k * (R + n).choose (k + 1) := Nat.mul_lt_mul_of_pos_right hbad hb'
      _ = (R + n).choose (k + 1) * (R + n).choose k := by ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- The shells that cannot be moved form an upper tail of `{0, ..., R + n}`. -/
theorem bad_upper {R n w k k' : ℕ} (hkk : k ≤ k') (hk' : k' ≤ R + n)
    (hbad : R.choose (k + w) < (R + n).choose k) :
    R.choose (k' + w) < (R + n).choose k' := by
  induction k', hkk using Nat.le_induction with
  | base => exact hbad
  | succ m hm ih => exact bad_succ hk' (ih (by omega))

/-- When `C(R+n, k) ≤ C(R, k+w)`, the source shell embeds into the target shell; every source
state carries `k` excitations of the pool plus the battery's `w`, every target state `k + w`
reservoir excitations with the battery lowered, so the map conserves energy. -/
theorem shell_embedding (R n k w : ℕ) (h : (R + n).choose k ≤ R.choose (k + w)) :
    ∃ f : {s : Finset (Fin (R + n)) // s.card = k} ↪ {t : Finset (Fin R) // t.card = k + w},
      ∀ s, (f s).1.card + 0 = s.1.card + w := by
  have hc : Fintype.card {s : Finset (Fin (R + n)) // s.card = k}
      ≤ Fintype.card {t : Finset (Fin R) // t.card = k + w} := by
    rw [Fintype.card_finset_len, Fintype.card_finset_len, Fintype.card_fin, Fintype.card_fin]
    exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  exact ⟨f, fun s => by rw [(f s).2, s.2]; ring⟩

/-- Table 1: qubit counts `R + 2n + 7 + 1` for `n = 100`, and a 7-qubit counter suffices for
the `n + 2` labels of a round counter while 6 qubits do not. -/
theorem table_counts :
    2000 + 2 * 100 + 7 + 1 = 2208 ∧ 10000 + 2 * 100 + 7 + 1 = 10208 ∧
      50000 + 2 * 100 + 7 + 1 = 50208 ∧ 100 + 2 ≤ 2 ^ 7 ∧ 2 ^ 6 < 100 + 2 := by
  norm_num

set_option exponentiation.threshold 512 in
/-- `n = 234`: `w = 137` is the least integer with `2^w ≥ (3/2)^234`. -/
theorem prep_234 : 3 ^ 234 ≤ 2 ^ (137 + 234) ∧ 2 ^ (136 + 234) < 3 ^ 234 := by
  norm_num

/-- `n = 234`: a refund from `2^5 = 32` positions keeps `8 · 2^r (5/6)^n ≤ (10^{-8} - 10^{-12})^2`
and `2^6` does not (cross-multiplied: `(10^{-8} - 10^{-12})^2 = 9999^2 / 10^{24}`). -/
theorem refund_234 :
    8 * 2 ^ 5 * 5 ^ 234 * 10 ^ 24 ≤ 9999 ^ 2 * 6 ^ 234 ∧
      9999 ^ 2 * 6 ^ 234 < 8 * 2 ^ 6 * 5 ^ 234 * 10 ^ 24 := by
  norm_num

/-- `n = 234`: the error `10^{-12} + √p`, `p = 8 · 32 (5/6)^234`, is below `8.71 · 10^{-9}`:
`p < (8.709 · 10^{-9})^2`, i.e. `256 · 5^234 · 10^{24} < 8709^2 · 6^234`. -/
theorem error_234 : 8 * 2 ^ 5 * 5 ^ 234 * 10 ^ 24 < 8709 ^ 2 * 6 ^ 234 := by
  norm_num

/-- The same in real numbers: `10^{-12} + √(8 · 32 (5/6)^234) < 8.71 · 10^{-9}`. -/
theorem error_234_real :
    (1 : ℝ) / 10 ^ 12 + Real.sqrt (8 * 2 ^ 5 * (5 / 6) ^ 234) < 871 / 10 ^ 11 := by
  have hp : (8 : ℝ) * 2 ^ 5 * (5 / 6) ^ 234 < (8709 / 10 ^ 12) ^ 2 := by
    have h := error_234
    have h' : ((8 * 2 ^ 5 * 5 ^ 234 * 10 ^ 24 : ℕ) : ℝ) < ((8709 ^ 2 * 6 ^ 234 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    rw [div_pow, div_pow]
    rw [lt_div_iff₀ (by positivity)]
    have e : (8 : ℝ) * 2 ^ 5 * (5 ^ 234 / 6 ^ 234) * (10 ^ 12) ^ 2
        = 8 * 2 ^ 5 * 5 ^ 234 * 10 ^ 24 / 6 ^ 234 := by ring
    rw [e, div_lt_iff₀ (by positivity)]
    linarith
  have hs : Real.sqrt (8 * 2 ^ 5 * (5 / 6) ^ 234) < 8709 / 10 ^ 12 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact hp
  have : (1 : ℝ) / 10 ^ 12 + 8709 / 10 ^ 12 = 871 / 10 ^ 11 := by norm_num
  linarith

set_option exponentiation.threshold 512 in
/-- `n = 256`: `w = 150`, refund `r = 11`, nominal work `150 - 11 = 139`. -/
theorem batch_256 :
    3 ^ 256 ≤ 2 ^ (150 + 256) ∧ 2 ^ (149 + 256) < 3 ^ 256 ∧
      8 * 2 ^ 11 * 5 ^ 256 * 10 ^ 24 ≤ 9999 ^ 2 * 6 ^ 256 ∧
      9999 ^ 2 * 6 ^ 256 < 8 * 2 ^ 12 * 5 ^ 256 * 10 ^ 24 ∧ 150 - 11 = 139 ∧ 137 - 5 = 132 := by
  norm_num

end FiniteDevice

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms FiniteDevice.ratio_mono
#print axioms FiniteDevice.bad_succ
#print axioms FiniteDevice.bad_upper
#print axioms FiniteDevice.shell_embedding
#print axioms FiniteDevice.table_counts
#print axioms FiniteDevice.prep_234
#print axioms FiniteDevice.refund_234
#print axioms FiniteDevice.error_234
#print axioms FiniteDevice.error_234_real
#print axioms FiniteDevice.batch_256
