import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.StarOrdered

/-!
# The two-qubit certificate: exact matrix identities (Appendix "The two-qubit certificate")

Registers are ordered `Q, A, B` (index `(Q × A) × B`).  All matrices below have integer entries
after scaling: `P4 = 4 Π_code`, and `Y ⊗ Y = -(XZ ⊗ XZ)` is real.  We prove

* `P4 = 1 + X_A X_B + Z_Q Z_A Z_B - Z_Q Y_A Y_B`, the stabilizer formula for the leakage;
* `P4` is symmetric with `P4² = 4 P4`, so `Π_code` is a projector;
* `2(1 - XX) + 2(1 - ZZZ) - (4 - P4) = (1 - XX)(1 - ZZZ)`, whose real form is positive
  semidefinite (`two_setting_psd`), so the leakage is at most `Pr[XX = -1] + Pr[ZZZ = -1]`;
* the decoder `V = P_+ ⊗ 1_Q + P_- ⊗ Z_Q` sends `√2 W|b⟩` to `√2 |b⟩|Φ+⟩` (scaled by 2).
-/

open Matrix
open scoped Kronecker

namespace Certificate

abbrev Idx := (Fin 2 × Fin 2) × Fin 2

def X : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def Z : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]
def I2 : Matrix (Fin 2) (Fin 2) ℤ := 1

def XX : Matrix Idx Idx ℤ := (I2 ⊗ₖ X) ⊗ₖ X
def ZZZ : Matrix Idx Idx ℤ := (Z ⊗ₖ Z) ⊗ₖ Z
/-- `Z_Q Y_A Y_B`, using `Y ⊗ Y = -(XZ ⊗ XZ)`. -/
def ZYY : Matrix Idx Idx ℤ := -((Z ⊗ₖ (X * Z)) ⊗ₖ (X * Z))

/-- `√2 |β_{0q}⟩ = |0,q⟩ + |1,1-q⟩` on `A × B`. -/
def v (q : Fin 2) (ab : Fin 2 × Fin 2) : ℤ :=
  if (ab.1 = 0 ∧ ab.2 = q) ∨ (ab.1 = 1 ∧ ab.2 = 1 - q) then 1 else 0

/-- `4 Π_code = 2 Σ_q |q⟩⟨q| ⊗ v_q v_qᵀ`. -/
def P4 : Matrix Idx Idx ℤ :=
  Matrix.of fun i j => if i.1.1 = j.1.1 then 2 * v i.1.1 (i.1.2, i.2) * v i.1.1 (j.1.2, j.2) else 0

theorem stabilizer_formula : P4 = 1 + XX + ZZZ - ZYY := by decide

theorem P4_symm : P4ᵀ = P4 := by decide

theorem P4_sq : P4 * P4 = 4 • P4 := by decide

def E : Matrix Idx Idx ℤ := (1 - XX) * (1 - ZZZ)

theorem two_setting_identity : 2 • (1 - XX) + 2 • (1 - ZZZ) - (4 • (1 : Matrix Idx Idx ℤ) - P4) = E := by
  decide

theorem E_symm : Eᵀ = E := by decide

theorem E_sq : E * E = 4 • E := by decide

/-- The real form of `E` is positive semidefinite, so `(1 - Π) ≤ (1 - XX)/2 + (1 - ZZZ)/2`. -/
theorem two_setting_psd : (E.map (Int.castRingHom ℝ)).PosSemidef := by
  set Er := E.map (Int.castRingHom ℝ)
  have hT : Erᴴ = Er := by
    rw [conjTranspose_eq_transpose_of_trivial, ← transpose_map, E_symm]
  have hsq : Er * Er = (4 : ℝ) • Er := by
    have h := congrArg (fun M => M.map (Int.castRingHom ℝ)) E_sq
    simp only [Matrix.map_mul] at h
    rw [h]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply]
    simp [Er]
  have hEr : Er = (4⁻¹ : ℝ) • (Erᴴ * Er) := by
    rw [hT, hsq, smul_smul]
    norm_num
  rw [hEr]
  exact (posSemidef_conjTranspose_mul_self Er).smul (by norm_num)

/-- `2V = 1_Q ⊗ (1 + X)_A ⊗ 1_B + Z_Q ⊗ (1 - X)_A ⊗ 1_B`. -/
def V2 : Matrix Idx Idx ℤ := (I2 ⊗ₖ (1 + X)) ⊗ₖ I2 + (Z ⊗ₖ (1 - X)) ⊗ₖ I2

/-- `√2 W|q⟩ = |q⟩ ⊗ (|0,q⟩ + |1,1-q⟩)`. -/
def w (q : Fin 2) : Idx → ℤ := fun i => if i.1.1 = q then v q (i.1.2, i.2) else 0

/-- `2 √2 |q⟩|Φ+⟩ = 2 |q⟩ ⊗ (|00⟩ + |11⟩)`. -/
def target (q : Fin 2) : Idx → ℤ := fun i => if i.1.1 = q then (if i.1.2 = i.2 then 2 else 0) else 0

theorem decoder (q : Fin 2) : V2 *ᵥ w q = target q := by
  fin_cases q <;> decide

end Certificate

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Certificate.stabilizer_formula
#print axioms Certificate.P4_symm
#print axioms Certificate.P4_sq
#print axioms Certificate.two_setting_identity
#print axioms Certificate.E_symm
#print axioms Certificate.E_sq
#print axioms Certificate.two_setting_psd
#print axioms Certificate.decoder
