import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The qutrit process: the scalar chain of the single-input bound (Appendix "A single input")

Throughout `0 < λ < 1`, `s = √(1-λ)`, `Δ = s - (1-λ)` and `k = 2λ(1+2s)/(1-λ)`.

* `Delta_pos`: `Δ_λ > 0`;
* `delta_eq`: `δ(λ) = (1-λ)Δ²/(4(1-λ)Δ + 2λ(1+2s)) = Δ²/(4Δ + k)`;
* `step2`, `step3`, `step4`, `single_input_bound`: from Step 1 (`|y| + |e| ≤ 2ε`,
  `e = (x - T21)/2`), Step 2 (`(s-y)² ≤ (s² + 2ε)(1 - T21)`) and the Lemma
  (`√(λx) ≥ Δ - y`), the error satisfies `ε ≥ δ(λ)`;
* `gibbs_forces`: a Gibbs-preserving stochastic matrix whose output populations on `ψ₀` are
  those of `Φ(ψ₀)` has `T01 = 0`, `T02 = 1` and `T20 = λ`;
* `lemma_value`, `f_le_z_deriv`, `tight`: the scalar facts behind Lemma "Coherence and
  transfer": `λ f(T20/λ) = λ - √(λ(λ - T20))` for `f(x) = 1 - √(1-x)`, `f(z) ≤ z f'(z)`, and the
  bound `1 - λ + √(λ(λ - T20))` equals `1 - λ + λa` at `T20 = λ(1 - a²)`;
* `pinsker_zero`: `u ≤ c√(2δ)` forces `δ ≥ u²/(2c²)`.
-/

namespace Qutrit

open Real

theorem Delta_pos {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : 0 < √(1 - l) - (1 - l) := by
  have ha : 0 < 1 - l := by linarith
  have hlt : 1 - l < √(1 - l) := by
    have hs : (1 - l) * (1 - l) < 1 - l := by nlinarith
    calc 1 - l = √((1 - l) * (1 - l)) := (Real.sqrt_mul_self ha.le).symm
      _ < √(1 - l) := Real.sqrt_lt_sqrt (by positivity) hs
  linarith

theorem delta_eq {l : ℝ} (h0 : 0 < l) (h1 : l < 1) :
    (1 - l) * (√(1 - l) - (1 - l)) ^ 2 / (4 * (1 - l) * (√(1 - l) - (1 - l)) + 2 * l * (1 + 2 * √(1 - l)))
      = (√(1 - l) - (1 - l)) ^ 2 / (4 * (√(1 - l) - (1 - l)) + 2 * l * (1 + 2 * √(1 - l)) / (1 - l)) := by
  have ha : 0 < 1 - l := by linarith
  have hD := Delta_pos h0 h1
  have hs : 0 ≤ √(1 - l) := Real.sqrt_nonneg _
  have hden1 : 0 < 4 * (1 - l) * (√(1 - l) - (1 - l)) + 2 * l * (1 + 2 * √(1 - l)) := by positivity
  have hden2 : 0 < 4 * (√(1 - l) - (1 - l)) + 2 * l * (1 + 2 * √(1 - l)) / (1 - l) := by positivity
  rw [div_eq_div_iff hden1.ne' hden2.ne']
  field_simp

/-- Step 2: `T21 (1 - λ) ≤ 2ε + 2s max(y, 0)`. -/
theorem step2 {l eps y T21 : ℝ} (h0 : 0 < l) (h1 : l < 1) (heps : 0 ≤ eps) (hT : 0 ≤ T21)
    (h : (√(1 - l) - y) ^ 2 ≤ (√(1 - l) ^ 2 + 2 * eps) * (1 - T21)) :
    T21 * (1 - l) ≤ 2 * eps + 2 * √(1 - l) * max y 0 := by
  have ha : 0 < 1 - l := by linarith
  have hsq : √(1 - l) ^ 2 = 1 - l := Real.sq_sqrt ha.le
  have hs : 0 ≤ √(1 - l) := Real.sqrt_nonneg _
  rw [hsq] at h
  -- T21 (1 - l + 2 eps) <= 2 eps + 2 s y - y^2
  have key : T21 * (1 - l + 2 * eps) ≤ 2 * eps + 2 * √(1 - l) * y - y ^ 2 := by nlinarith
  have hm : 2 * √(1 - l) * y ≤ 2 * √(1 - l) * max y 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  nlinarith [sq_nonneg y]

/-- Step 3: `λ x ≤ k ε`, written without division as `x (1 - λ) ≤ 2(1 + 2s) ε`. -/
theorem step3 {l eps y x T21 : ℝ} (h0 : 0 < l) (h1 : l < 1) (heps : 0 ≤ eps)
    (hS1 : |y| + |(x - T21) / 2| ≤ 2 * eps)
    (h2 : T21 * (1 - l) ≤ 2 * eps + 2 * √(1 - l) * max y 0) :
    x * (1 - l) ≤ 2 * (1 + 2 * √(1 - l)) * eps := by
  have ha : 0 < 1 - l := by linarith
  set s := √(1 - l) with hsdef
  have hsq : s ^ 2 = 1 - l := Real.sq_sqrt ha.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    rw [hsdef, Real.sqrt_le_one]
    linarith
  have hsa : 1 - l ≤ s := by nlinarith
  have he : (x - T21) / 2 ≤ |(x - T21) / 2| := le_abs_self _
  have hx : x ≤ 2 * (2 * eps - |y|) + T21 := by linarith
  have hya : |y| ≤ 2 * eps := by linarith [abs_nonneg ((x - T21) / 2)]
  rcases le_or_gt 0 y with hy | hy
  · rw [max_eq_left hy] at h2
    rw [abs_of_nonneg hy] at hx hya
    have hxa : x * (1 - l) ≤ 2 * (2 * eps - y) * (1 - l) + T21 * (1 - l) := by nlinarith
    have hsy : 2 * y * (s - (1 - l)) ≤ 2 * (2 * eps) * (s - (1 - l)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · rw [max_eq_right hy.le] at h2
    rw [abs_of_neg hy] at hx hya
    have hxa : x * (1 - l) ≤ 2 * (2 * eps + y) * (1 - l) + T21 * (1 - l) := by nlinarith
    nlinarith

/-- Step 4: if `Δ - y ≤ √(λx)`, `y ≤ 2ε` and `λx ≤ kε`, then `ε ≥ Δ²/(4Δ + k)`. -/
theorem step4 {D k eps y lx : ℝ} (hD : 0 < D) (hk : 0 ≤ k) (heps : 0 ≤ eps) (hy : y ≤ 2 * eps)
    (hlx : 0 ≤ lx) (hL : D - y ≤ √lx) (h3 : lx ≤ k * eps) : D ^ 2 / (4 * D + k) ≤ eps := by
  have hden : 0 < 4 * D + k := by linarith
  rw [div_le_iff₀ hden]
  rcases lt_or_ge (2 * eps) D with h | h
  · have hpos : 0 < D - 2 * eps := by linarith
    have h1 : D - 2 * eps ≤ √lx := by linarith
    have h2 : (D - 2 * eps) ^ 2 ≤ lx := by
      calc (D - 2 * eps) ^ 2 ≤ √lx ^ 2 := pow_le_pow_left₀ hpos.le h1 2
        _ = lx := Real.sq_sqrt hlx
    nlinarith
  · nlinarith

/-- The single-input bound: Steps 1-4 and the Lemma give `ε ≥ δ(λ)`. -/
theorem single_input_bound {l eps y x T21 : ℝ} (h0 : 0 < l) (h1 : l < 1) (heps : 0 ≤ eps)
    (hT : 0 ≤ T21) (hx0 : 0 ≤ x)
    (hS1 : |y| + |(x - T21) / 2| ≤ 2 * eps)
    (hS2 : (√(1 - l) - y) ^ 2 ≤ (√(1 - l) ^ 2 + 2 * eps) * (1 - T21))
    (hL : (√(1 - l) - (1 - l)) - y ≤ √(l * x)) :
    (1 - l) * (√(1 - l) - (1 - l)) ^ 2 / (4 * (1 - l) * (√(1 - l) - (1 - l)) + 2 * l * (1 + 2 * √(1 - l)))
      ≤ eps := by
  have ha : 0 < 1 - l := by linarith
  have hD := Delta_pos h0 h1
  have h2 := step2 h0 h1 heps hT hS2
  have h3 := step3 h0 h1 heps hS1 h2
  set k := 2 * l * (1 + 2 * √(1 - l)) / (1 - l) with hk
  have hk0 : 0 ≤ k := by positivity
  have hlx : l * x ≤ k * eps := by
    rw [hk, div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith
  have hy : y ≤ 2 * eps := by
    have := le_abs_self y
    linarith [abs_nonneg ((x - T21) / 2)]
  rw [delta_eq h0 h1]
  exact step4 hD hk0 heps hy (by positivity) hL hlx

/-- Gibbs preservation with the populations of `Φ(ψ₀)` forces `T01 = 0`, `T02 = 1`, `T20 = λ`.
The Gibbs vector is `(1, r, λ)` up to normalization, with `r = e^{-βE1} < 1`; only the rows of
levels 0 and 2, the column sum of input 2, the populations of outputs 0 and 2 and the signs of
five entries are needed. -/
theorem gibbs_forces {T00 T01 T02 T12 T20 T21 T22 r l : ℝ}
    (h00 : 0 ≤ T00) (h01 : 0 ≤ T01) (h12 : 0 ≤ T12) (h21 : 0 ≤ T21) (h22 : 0 ≤ T22)
    (hr : r < 1) (hl : 0 < l) (c2 : T02 + T12 + T22 = 1)
    (g0 : T00 + T01 * r + T02 * l = 1) (g2 : T20 + T21 * r + T22 * l = l)
    (p0 : T00 + T01 = 1 - l) (p2 : T20 + T21 = l) :
    T01 = 0 ∧ T02 = 1 ∧ T20 = l := by
  have key : l * (T02 - 1) = T01 * (1 - r) := by linarith
  have hT02 : T02 ≤ 1 := by linarith
  have hlhs : l * (T02 - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)
  have hrhs : 0 ≤ T01 * (1 - r) := mul_nonneg h01 (by linarith)
  have hT01 : T01 * (1 - r) = 0 := by linarith
  have e01 : T01 = 0 := by
    rcases mul_eq_zero.mp hT01 with h | h
    · exact h
    · linarith
  have e02 : T02 = 1 := by
    have : l * (T02 - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have e22 : T22 = 0 := by linarith
  have e21 : T21 = 0 := by
    have : T21 * (1 - r) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  exact ⟨e01, e02, by linarith⟩

/-- `λ f(T/λ) = λ - √(λ(λ - T))` for `f(x) = 1 - √(1 - x)` and `0 ≤ T ≤ λ`. -/
theorem lemma_value {l T : ℝ} (hl : 0 < l) :
    l * (1 - √(1 - T / l)) = l - √(l * (l - T)) := by
  have h : l * (l - T) = l ^ 2 * (1 - T / l) := by field_simp
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hl.le]
  ring

/-- `f(z) ≤ z f'(z)` for `f(z) = 1 - √(1 - z)`, `0 ≤ z < 1`, so `W f(T/W)` does not increase with
`W`. -/
theorem f_le_z_deriv {z : ℝ} (hz1 : z < 1) :
    1 - √(1 - z) ≤ z / (2 * √(1 - z)) := by
  have ha : 0 < 1 - z := by linarith
  have hs : 0 < √(1 - z) := Real.sqrt_pos.mpr ha
  have hsq : √(1 - z) ^ 2 = 1 - z := Real.sq_sqrt ha.le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 - √(1 - z))]

/-- Tightness: at `T20 = λ(1 - a²)` the bound `1 - λ + √(λ(λ - T20))` equals `1 - λ + λa`, the
coherence `c` of the truncated oscillator in the limit `W → λ`. -/
theorem tight {l a : ℝ} (hl : 0 ≤ l) (ha : 0 ≤ a) :
    1 - l + √(l * (l - l * (1 - a ^ 2))) = 1 - l + l * a := by
  have h : l * (l - l * (1 - a ^ 2)) = (l * a) ^ 2 := by ring
  rw [h, Real.sqrt_sq (by positivity)]

/-- With zero Gibbs defect the Pinsker form `G ≥ (2/ln 2)[u - c√(2δ)]₊²` forces `u ≤ c√(2δ)`, hence
`δ ≥ u²/(2c²)`. -/
theorem pinsker_zero {u c δ : ℝ} (hc : 0 < c) (hu : 0 ≤ u) (hδ : 0 ≤ δ) (h : u ≤ c * √(2 * δ)) :
    u ^ 2 / (2 * c ^ 2) ≤ δ := by
  have h2 : u ^ 2 ≤ (c * √(2 * δ)) ^ 2 := pow_le_pow_left₀ hu h 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h2
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Qutrit

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Qutrit.Delta_pos
#print axioms Qutrit.delta_eq
#print axioms Qutrit.step2
#print axioms Qutrit.step3
#print axioms Qutrit.step4
#print axioms Qutrit.single_input_bound
#print axioms Qutrit.gibbs_forces
#print axioms Qutrit.lemma_value
#print axioms Qutrit.f_le_z_deriv
#print axioms Qutrit.tight
#print axioms Qutrit.pinsker_zero
