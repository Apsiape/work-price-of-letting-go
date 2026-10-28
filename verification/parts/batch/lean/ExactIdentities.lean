import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact identities of the examples

* `Arrow`: the qutrit channel `N` of Proposition "A process and its reverse can cost differently",
  in the basis `|+⟩, |-⟩, |2⟩`, with symbolic `a = kT ln(3/2)`, `b = kT ln 3`: the change of basis,
  the POVM, Gibbs preservation, the energy change `D`, the coherence `⟨+|H - N^*(H)|-⟩ = -a/2`, the dual
  certificate `D - Ψ^*(Y) = -(a/2)[[t,-1,0],[-1,1/t,0],[0,0,0]]` for every `t > 0`, and the positivity of
  that matrix.
* `Theta`: the family of Proposition "The asymmetry is not generic": a POVM, Gibbs-preserving, with
  `⟨u|H|v⟩ = a sin θ cos θ`, for all `c = cos θ`, `s = sin θ` with `c² + s² = 1`.
* `GPQutrit`: Proposition "Gibbs preservation is not enough": completeness, Gibbs preservation, the
  fixed point `σ`, equal environment states `diag(1 - y², y²)` for `|0⟩⟨0|` and `σ`, and `Tr ρD = y² E_1`.
* `Reach`: Proposition "A Gibbs-preserving channel that reaches its capacity": `det σ_0 = 1/6`,
  `det σ_1 = 0`, `(3/4)σ_0 + (1/4)σ_1 = γ`, and the capacity `β^{-1}(ln 2 - S(γ)) = E(3/4 - ln2/ln3)`.
* `xdephasing_excess`: `E/2 - β^{-1} ln cosh(βE/2) = β^{-1} ln[2/(1 + e^{-βE})]` (Theorem "Waiting does not
  help").
* `Bell`: for `H = E(I - |Φ⁺⟩⟨Φ⁺|)` and `Φ = id ⊗ R`, `Φ^*(H) = (3/4)E I` and `H|Φ⁺⟩ = 0`.
* `Bank`: the flat bank, for every `L`: the branch weights, the common law after the step, the total
  rank `k = L(L+1)(L+2)/3`, a fair branch, the return distance `6/((L+1)(L+2))`, equal means, and the
  drop of the variance by exactly one level squared.
-/

open Matrix

noncomputable section

namespace KeepingTime

namespace Arrow

/-- Columns `|+⟩, |-⟩, |2⟩` in the computational basis, with `s = 1/√2`. -/
def U (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![s, s, 0; s, -s, 0; 0, 0, 1]

def M0 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 1 / 2]
def M1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 4 / 5, 0; 0, 0, 0]
def M2 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 1 / 5, 0; 0, 0, 1 / 2]

/-- `H` and `γ` in the basis `|+⟩, |-⟩, |2⟩`. -/
def Hpm (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![a / 2, -a / 2, 0; -a / 2, a / 2, 0; 0, 0, b]
def gpm : Matrix (Fin 3) (Fin 3) ℝ := !![5 / 12, 1 / 12, 0; 1 / 12, 5 / 12, 0; 0, 0, 1 / 6]

/-- `N^*(H) = Σ_i H_ii M_i` with `H = diag(0, a, b)` at the output, in the input basis `(+,-,2)`. -/
def NstarH (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (0 : ℝ) • M0 + a • M1 + b • M2

def Dpm (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-a / 2, a / 2, 0; a / 2, 3 * a / 10 + b / 5, 0; 0, 0, -b / 2]

theorem basis_orthonormal (s : ℝ) (hs : s ^ 2 = 1 / 2) : (U s)ᵀ * U s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [hs]

theorem H_in_basis (a b s : ℝ) (hs : s ^ 2 = 1 / 2) :
    (U s)ᵀ * diagonal ![0, a, b] * U s = Hpm a b := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U, Hpm, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination a * hs | linear_combination (-a) * hs

theorem gamma_in_basis (s : ℝ) (hs : s ^ 2 = 1 / 2) :
    (U s)ᵀ * diagonal ![1 / 2, 1 / 3, 1 / 6] * U s = gpm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U, gpm, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (5 / 6 : ℝ) * hs | linear_combination (1 / 6 : ℝ) * hs

theorem povm : M0 + M1 + M2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [M0, M1, M2]

/-- `N(γ) = γ`: the output populations are `(1/2, 1/3, 1/6)`. -/
theorem gibbs_preserving : trace (M0 * gpm) = 1 / 2 ∧ trace (M1 * gpm) = 1 / 3 ∧ trace (M2 * gpm) = 1 / 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [M0, M1, M2, gpm, trace, Fin.sum_univ_three] <;> norm_num

theorem energy_change (a b : ℝ) : NstarH a b - Hpm a b = Dpm a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [NstarH, Hpm, Dpm, M0, M1, M2] <;> ring

theorem coherence (a b : ℝ) : (Hpm a b - NstarH a b) 0 1 = -(a / 2) := by
  simp [NstarH, Hpm, M0, M1, M2]; ring

/-- The output weights `Q_is = (M_i)_ss`; every column sums to one, so `Ψ^*(Y) = diag(X)` for
`Y_(i,s) = X_s`. -/
def Q : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1 / 2; 0, 4 / 5, 0; 0, 1 / 5, 1 / 2]

theorem Q_columns (s : Fin 3) : ∑ i, Q i s = 1 := by
  fin_cases s <;> simp [Q, Fin.sum_univ_three] <;> norm_num

theorem Q_is_M (s : Fin 3) : Q 0 s = M0 s s ∧ Q 1 s = M1 s s ∧ Q 2 s = M2 s s := by
  fin_cases s <;> simp [Q, M0, M1, M2]

def Xcert (a b t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal ![a / 2 * (t - 1), (3 * a + 2 * b) / 10 + a / (2 * t), -b / 2]

def Ccert (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![t, -1, 0; -1, 1 / t, 0; 0, 0, 0]

theorem dual_certificate (a b t : ℝ) : Dpm a b - Xcert a b t = (-(a / 2)) • Ccert t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dpm, Xcert, Ccert] <;> ring

theorem certificate_psd (t : ℝ) (ht : 0 < t) (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ (Ccert t *ᵥ v) := by
  simp [Ccert, dotProduct, mulVec, Fin.sum_univ_three]
  have e : v 0 * (t * v 0 + -v 1) + v 1 * (-v 0 + t⁻¹ * v 1) = (t * v 0 - v 1) ^ 2 / t := by
    field_simp; ring
  rw [e]; positivity

end Arrow

namespace Theta

def u (c s : ℝ) : Fin 3 → ℝ := ![c, s, 0]
def v (c s : ℝ) : Fin 3 → ℝ := ![-s, c, 0]
def e2 : Fin 3 → ℝ := ![0, 0, 1]

def M0 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := vecMulVec (u c s) (u c s) + s ^ 2 • vecMulVec e2 e2
def M1 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (2 / (2 + s ^ 2)) • vecMulVec (v c s) (v c s)
def M2 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (s ^ 2 / (2 + s ^ 2)) • vecMulVec (v c s) (v c s) + (1 - s ^ 2) • vecMulVec e2 e2

def gam : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1 / 2, 1 / 3, 1 / 6]

theorem povm (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : M0 c s + M1 c s + M2 c s = 1 := by
  have hp : (2 + s ^ 2) ≠ 0 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M0, M1, M2, u, v, e2, vecMulVec, Matrix.vecHead, Matrix.vecTail] <;>
    first | ring1 | (field_simp; ring1) | (field_simp; linear_combination (2 + s ^ 2) * h)

theorem gibbs0 (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : trace (M0 c s * gam) = 1 / 2 := by
  have e : trace (M0 c s * gam) = c ^ 2 / 2 + s ^ 2 / 3 + s ^ 2 / 6 := by
    simp [M0, u, e2, gam, vecMulVec, trace, Matrix.mul_apply, Fin.sum_univ_three]; ring
  rw [e]; linear_combination (1 / 2 : ℝ) * h

theorem gibbs1 (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : trace (M1 c s * gam) = 1 / 3 := by
  have hp : (2 + s ^ 2) ≠ 0 := by positivity
  have e : trace (M1 c s * gam) = 2 * (s ^ 2 / 2 + c ^ 2 / 3) / (2 + s ^ 2) := by
    simp [M1, v, gam, vecMulVec, trace, Matrix.mul_apply, Fin.sum_univ_three]; ring
  rw [e, div_eq_iff hp]; linear_combination (2 / 3 : ℝ) * h

theorem gibbs2 (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : trace (M2 c s * gam) = 1 / 6 := by
  have hp : (2 + s ^ 2) ≠ 0 := by positivity
  have e : trace (M2 c s * gam) = (s ^ 2 * (s ^ 2 / 2 + c ^ 2 / 3) + (1 - s ^ 2) * (2 + s ^ 2) / 6) / (2 + s ^ 2) := by
    simp [M2, v, e2, gam, vecMulVec, trace, Matrix.mul_apply, Fin.sum_univ_three]; field_simp
  rw [e, div_eq_iff hp]; linear_combination (s ^ 2 / 3 : ℝ) * h

theorem coherence (a b c s : ℝ) : u c s ⬝ᵥ (diagonal ![0, a, b] *ᵥ v c s) = a * s * c := by
  simp [u, v, dotProduct, mulVec, diagonal, Fin.sum_univ_three]; ring

end Theta

namespace GPQutrit

def K0 (α0 α1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![α0, 0, 0; 0, α1, 0; 0, 0, 1]
def K1 (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, x, 0; y, 0, 0; 0, 0, 0]
def K1t (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, y, 0; x, 0, 0; 0, 0, 0]
def gam (e g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, e, 0; 0, 0, g]
def sig (e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 / 2, 0, 0; 0, e / 2, 0; 0, 0, (1 - e) / 2]
def rho0 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
def Hq (E1 E2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, E1, 0; 0, 0, E2]

theorem transposes (α0 α1 x y : ℝ) : (K0 α0 α1)ᵀ = K0 α0 α1 ∧ (K1 x y)ᵀ = K1t x y := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl

variable {α0 α1 x y e : ℝ}

theorem complete (h0 : α0 ^ 2 = 1 - y ^ 2) (h1 : α1 ^ 2 = 1 - x ^ 2) :
    K0 α0 α1 * K0 α0 α1 + K1t x y * K1 x y = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K0, K1, K1t] <;>
    first | ring1 | linear_combination h0 | linear_combination h1

theorem gibbs_preserving (g : ℝ) (h0 : α0 ^ 2 = 1 - y ^ 2) (h1 : α1 ^ 2 = 1 - x ^ 2) (hxy : x ^ 2 * e = y ^ 2) :
    K0 α0 α1 * gam e g * K0 α0 α1 + K1 x y * gam e g * K1t x y = gam e g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K0, K1, K1t, gam] <;>
    first | ring1 | linear_combination h0 + hxy | linear_combination e * h1 - hxy

theorem fixed_point (h0 : α0 ^ 2 = 1 - y ^ 2) (h1 : α1 ^ 2 = 1 - x ^ 2) (hxy : x ^ 2 * e = y ^ 2) :
    K0 α0 α1 * sig e * K0 α0 α1 + K1 x y * sig e * K1t x y = sig e := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K0, K1, K1t, sig] <;>
    first | ring1 | linear_combination (h0 + hxy) / 2 | linear_combination (e * h1 - hxy) / 2

/-- The environment state `Ψ(ρ)_{kl} = Tr K_k ρ K_l^T`. -/
def psi (α0 α1 x y : ℝ) (ρ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![trace (K0 α0 α1 * ρ * K0 α0 α1), trace (K0 α0 α1 * ρ * K1t x y);
     trace (K1 x y * ρ * K0 α0 α1), trace (K1 x y * ρ * K1t x y)]

theorem same_environment (h0 : α0 ^ 2 = 1 - y ^ 2) (h1 : α1 ^ 2 = 1 - x ^ 2) (hxy : x ^ 2 * e = y ^ 2) :
    psi α0 α1 x y rho0 = !![1 - y ^ 2, 0; 0, y ^ 2] ∧
      psi α0 α1 x y (sig e) = !![1 - y ^ 2, 0; 0, y ^ 2] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [psi, K0, K1, K1t, rho0, sig, trace, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination h0 | linear_combination (h0 + e * h1 - hxy) / 2 |
      linear_combination hxy / 2

theorem energy_gain (E1 E2 : ℝ) :
    (K0 α0 α1 * Hq E1 E2 * K0 α0 α1 + K1t x y * Hq E1 E2 * K1 x y - Hq E1 E2) 0 0 = y ^ 2 * E1 := by
  simp [K0, K1, K1t, Hq]; ring

end GPQutrit

namespace Reach

def σ0 (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, r / 12; r / 12, 1 / 4]
def σ1 (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, -r / 4; -r / 4, 1 / 4]

theorem states (r : ℝ) (hr : r ^ 2 = 3) :
    det (σ0 r) = 1 / 6 ∧ det (σ1 r) = 0 ∧ (3 / 4 : ℝ) • σ0 r + (1 / 4 : ℝ) • σ1 r = diagonal ![3 / 4, 1 / 4] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [det_fin_two]; simp [σ0]; linear_combination (-1 / 144 : ℝ) * hr
  · rw [det_fin_two]; simp [σ1]; linear_combination (-1 / 16 : ℝ) * hr
  · ext i j; fin_cases i <;> fin_cases j <;> simp [σ0, σ1] <;> ring

/-- `β^{-1}[ln 2 - S(γ)] = E(3/4 - ln 2/ln 3)` for `γ = diag(3/4, 1/4)` and `βE = ln 3`. -/
theorem capacity_value (E : ℝ) :
    (Real.log 2 - (-(3 / 4 * Real.log (3 / 4)) - 1 / 4 * Real.log (1 / 4))) / (Real.log 3 / E) =
      E * (3 / 4 - Real.log 2 / Real.log 3) := by
  have h3 : Real.log 3 ≠ 0 := by positivity
  have e1 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have e2 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  rw [e1, e2]
  rcases eq_or_ne E 0 with hE | hE
  · subst hE; simp
  · field_simp; ring

end Reach

/-- Theorem "Waiting does not help": the excess of the batch cost `E/2` over the capacity
`β^{-1} ln cosh(βE/2)` is `β^{-1} ln[2/(1 + e^{-βE})]`. -/
theorem xdephasing_excess (β E : ℝ) (hβ : 0 < β) :
    E / 2 - Real.log (Real.cosh (β * E / 2)) / β = Real.log (2 / (1 + Real.exp (-(β * E)))) / β := by
  set t := Real.exp (β * E / 2) with ht
  have tpos : 0 < t := Real.exp_pos _
  have hneg : Real.exp (-(β * E)) = (t ^ 2)⁻¹ := by
    rw [ht, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  have hcosh : Real.cosh (β * E / 2) = (t + t⁻¹) / 2 := by
    rw [Real.cosh_eq, ht, Real.exp_neg]
  have key : 2 / (1 + Real.exp (-(β * E))) = t / Real.cosh (β * E / 2) := by
    rw [hneg, hcosh]; field_simp
  have hc : 0 < Real.cosh (β * E / 2) := Real.cosh_pos _
  rw [key, Real.log_div tpos.ne' hc.ne', ht, Real.log_exp]
  field_simp

namespace Bell

/-- Two qubits indexed by `Fin 2 × Fin 2`; `p = |00⟩ + |11⟩` (so `|Φ⁺⟩⟨Φ⁺| = p pᵀ/2`). -/
def p : Fin 2 × Fin 2 → ℝ := fun ab => if ab.1 = ab.2 then 1 else 0

def H (E : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := E • (1 - (1 / 2 : ℝ) • vecMulVec p p)

/-- `Φ^*(X) = Tr_B(X)/2 ⊗ I` for `Φ = id_A ⊗ R_B`. -/
def phistar (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun i j => (∑ b, X (i.1, b) (j.1, b)) / 2 * (if i.2 = j.2 then 1 else 0)

theorem phistar_H (E : ℝ) : phistar (H E) = (3 / 4 * E) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [phistar, H, p, vecMulVec, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem H_kills_phi (E : ℝ) : H E *ᵥ p = 0 := by
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [H, p, mulVec, dotProduct, vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply] <;> ring

end Bell

namespace Bank

/-- Branch weights (times `k`): from level `j` the bank moves up with weight `(j+1)(L-j)` and down with
weight `(j-1)(L+2-j)`; at the ends all weight `L` moves inward. -/
def up (L j : ℚ) : ℚ := (j + 1) * (L - j)
def down (L j : ℚ) : ℚ := (j - 1) * (L + 2 - j)

/-- The split adds up to the initial interior rank `2j(L+1-j) - 2`. -/
theorem split (L j : ℚ) : up L j + down L j = 2 * j * (L + 1 - j) - 2 := by unfold up down; ring

theorem ends (L : ℚ) : up L 0 = L ∧ down L (L + 1) = L ∧ down L 1 = 0 ∧ up L L = 0 := by
  unfold up down; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- After the step the bank law is the same on both branches: level `l` receives `l(L+1-l)` from
each, half of the final interior rank `2l(L+1-l)`. -/
theorem same_law (L l : ℚ) : down L (l + 1) = l * (L + 1 - l) ∧ up L (l - 1) = l * (L + 1 - l) := by
  unfold up down; constructor <;> ring

lemma sum_interior (L : ℚ) (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℚ) + 1) * (L - j) = L * m * (m + 1) / 2 - (m - 1) * m * (m + 1) / 3 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The total rank: `Σ_{j=1}^{L} 2j(L+1-j) = L(L+1)(L+2)/3 = k`, before and after. -/
theorem total_rank (L : ℕ) :
    ∑ j ∈ Finset.range L, 2 * ((j : ℚ) + 1) * ((L : ℚ) + 1 - (j + 1)) = (L : ℚ) * (L + 1) * (L + 2) / 3 := by
  have := sum_interior (L : ℚ) L
  have e : ∀ j : ℕ, 2 * ((j : ℚ) + 1) * ((L : ℚ) + 1 - (j + 1)) = 2 * (((j : ℚ) + 1) * ((L : ℚ) - j)) := by
    intro j; ring
  simp_rw [e, ← Finset.mul_sum, this]
  ring

lemma sum_down (N : ℚ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (i : ℚ) * (N - i) = N * m * (m - 1) / 2 - (m - 1) * m * (2 * m - 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The branch is fair: the down weights `Σ_{i=0}^{L} i(L+1-i)` add up to `k/2`. -/
theorem fair (L : ℕ) :
    ∑ i ∈ Finset.range (L + 1), (i : ℚ) * ((L : ℚ) + 1 - i) = (L : ℚ) * (L + 1) * (L + 2) / 6 := by
  rw [sum_down]; push_cast; ring

/-- Return distance: the laws differ by `2/k` at each of the `L` interior levels and `L/k` at each end,
so the total variation is `2L/k = 6/((L+1)(L+2))`. -/
theorem return_distance (L : ℕ) (hL : 0 < L) :
    2 * (L : ℚ) / ((L : ℚ) * (L + 1) * (L + 2) / 3) = 6 / (((L : ℚ) + 1) * (L + 2)) := by
  have : (0 : ℚ) < L := by exact_mod_cast hL
  field_simp; ring

lemma sum_lin (m : ℕ) : ∑ j ∈ Finset.range m, ((j : ℚ) + 1) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Equal means: `Σ_j j (n_p(j) - n_q(j)) = (L+1)L - 2 Σ_{j=1}^{L} j = 0`. -/
theorem equal_means (L : ℕ) : 0 * (L : ℚ) + ((L : ℚ) + 1) * L - 2 * ∑ j ∈ Finset.range L, ((j : ℚ) + 1) = 0 := by
  rw [sum_lin]; ring

lemma sum_sq_shift (c : ℚ) (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℚ) + 1 - c) ^ 2 = m * (m + 1) * (2 * m + 1) / 6 - c * m * (m + 1) + m * c ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The variance drops by one level squared: `Σ_j (j - (L+1)/2)² (n_p(j) - n_q(j)) = k`, i.e.
`2L((L+1)/2)² - 2 Σ_{j=1}^{L} (j - (L+1)/2)² = L(L+1)(L+2)/3`. -/
theorem variance_drop (L : ℕ) :
    2 * (L : ℚ) * (((L : ℚ) + 1) / 2) ^ 2 - 2 * ∑ j ∈ Finset.range L, ((j : ℚ) + 1 - ((L : ℚ) + 1) / 2) ^ 2
      = (L : ℚ) * (L + 1) * (L + 2) / 3 := by
  rw [sum_sq_shift]; ring

end Bank

end KeepingTime

end

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms KeepingTime.Arrow.basis_orthonormal
#print axioms KeepingTime.Arrow.H_in_basis
#print axioms KeepingTime.Arrow.gamma_in_basis
#print axioms KeepingTime.Arrow.povm
#print axioms KeepingTime.Arrow.gibbs_preserving
#print axioms KeepingTime.Arrow.energy_change
#print axioms KeepingTime.Arrow.coherence
#print axioms KeepingTime.Arrow.Q_columns
#print axioms KeepingTime.Arrow.Q_is_M
#print axioms KeepingTime.Arrow.dual_certificate
#print axioms KeepingTime.Arrow.certificate_psd
#print axioms KeepingTime.Theta.povm
#print axioms KeepingTime.Theta.gibbs0
#print axioms KeepingTime.Theta.gibbs1
#print axioms KeepingTime.Theta.gibbs2
#print axioms KeepingTime.Theta.coherence
#print axioms KeepingTime.GPQutrit.transposes
#print axioms KeepingTime.GPQutrit.complete
#print axioms KeepingTime.GPQutrit.gibbs_preserving
#print axioms KeepingTime.GPQutrit.fixed_point
#print axioms KeepingTime.GPQutrit.same_environment
#print axioms KeepingTime.GPQutrit.energy_gain
#print axioms KeepingTime.Reach.states
#print axioms KeepingTime.Reach.capacity_value
#print axioms KeepingTime.xdephasing_excess
#print axioms KeepingTime.Bell.phistar_H
#print axioms KeepingTime.Bell.H_kills_phi
#print axioms KeepingTime.Bank.split
#print axioms KeepingTime.Bank.ends
#print axioms KeepingTime.Bank.same_law
#print axioms KeepingTime.Bank.total_rank
#print axioms KeepingTime.Bank.fair
#print axioms KeepingTime.Bank.return_distance
#print axioms KeepingTime.Bank.equal_means
#print axioms KeepingTime.Bank.variance_drop
