import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Exponent bookkeeping of Appendices B and D

* `step6_exponent`, `step6_rpow_mesh`, `step6_rpow_cross`: with `L = g^{-1/(2r)}`, both `L^{-1/3}` and
  `g^{1/4} L^{r/2 - 1/3}` equal `g^{1/(6r)}` (Appendix D, Step 6), and for `r ≤ 1` a mesh `g^{1/6}` gives
  `(g^{1/2}/g^{1/6})^{1/2} = g^{1/6}` (`step6_r_le_one`);
* `step7_energy`: the lattice isometries `J_{j,k}|e,b⟩ = |e, b, k - a_e⟩` turn `H_j + H'_B + H_L` into
  `H_{0j} + H'_B + const`: `(E_* + a·ω) + (E_L⁰ + (k - a)·(ω - ω₀)) = (E_* + a·ω₀) + (E_L⁰ + k·(ω - ω₀))`;
* `b4_exponent`: with `s = γ = N^{-1/8}` and `K_s ∝ 1/s`, the Chernoff exponent `N γ²/K_s` is `N^{5/8}`
  (Appendix B.4).
-/

open Real

namespace Repair

theorem step6_exponent (r : ℝ) (hr : 0 < r) : 1 / 4 - (1 / (2 * r)) * (r / 2 - 1 / 3) = 1 / (6 * r) := by
  field_simp
  ring

theorem step6_rpow_mesh (g r : ℝ) (hg : 0 < g) (hr : 0 < r) :
    (g ^ (-(1 / (2 * r)))) ^ (-(1 / 3 : ℝ)) = g ^ (1 / (6 * r)) := by
  rw [← rpow_mul hg.le]
  congr 1
  field_simp
  ring

theorem step6_rpow_cross (g r : ℝ) (hg : 0 < g) (hr : 0 < r) :
    g ^ (1 / 4 : ℝ) * (g ^ (-(1 / (2 * r)))) ^ (r / 2 - 1 / 3) = g ^ (1 / (6 * r)) := by
  rw [← rpow_mul hg.le, ← rpow_add hg]
  congr 1
  field_simp
  ring

theorem step6_r_le_one (g : ℝ) (hg : 0 < g) : (g ^ (1 / 2 : ℝ) / g ^ (1 / 6 : ℝ)) ^ (1 / 2 : ℝ) = g ^ (1 / 6 : ℝ) := by
  rw [← rpow_sub hg, ← rpow_mul hg.le]
  norm_num

theorem step7_energy {r : Type*} [Fintype r] (Es EL : ℝ) (a k ω ω₀ : r → ℝ) :
    (Es + a ⬝ᵥ ω) + (EL + (k - a) ⬝ᵥ (ω - ω₀)) = (Es + a ⬝ᵥ ω₀) + (EL + k ⬝ᵥ (ω - ω₀)) := by
  simp only [sub_dotProduct, dotProduct_sub]
  ring

theorem b4_exponent (N : ℝ) (hN : 0 < N) :
    N * (N ^ (-(1 / 8 : ℝ))) ^ (2 : ℕ) / N ^ (1 / 8 : ℝ) = N ^ (5 / 8 : ℝ) := by
  rw [← rpow_natCast, ← rpow_mul hN.le, div_eq_mul_inv, ← rpow_neg hN.le]
  conv_lhs => rw [show N * N ^ (-(1 / 8 : ℝ) * ((2 : ℕ) : ℝ)) * N ^ (-(1 / 8 : ℝ)) =
    N ^ (1 : ℝ) * N ^ (-(1 / 8 : ℝ) * ((2 : ℕ) : ℝ)) * N ^ (-(1 / 8 : ℝ)) by rw [rpow_one]]
  rw [← rpow_add hN, ← rpow_add hN]
  norm_num

end Repair

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Repair.step6_exponent
#print axioms Repair.step6_rpow_mesh
#print axioms Repair.step6_rpow_cross
#print axioms Repair.step6_r_le_one
#print axioms Repair.step7_energy
#print axioms Repair.b4_exponent
