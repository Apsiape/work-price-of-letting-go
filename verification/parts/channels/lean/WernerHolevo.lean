import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The Werner–Holevo channel: exact identities (Section 5, Appendix "The Werner–Holevo support test")

Scaled by `√2`, the Stinespring isometry `V|i⟩ = Σ_{jk} ε_{ijk} |j⟩|k⟩/√2` has integer entries.
Write `V2 = √2 V` and `W2 = 2W`, so `W2(Y) = Tr(Y) I - Yᵀ`.  We prove over `ℤ`:

* `V2_isometry`: `V2ᵀ V2 = 2 I`, so `V` is an isometry;
* `V2_proj`: `V2 V2ᵀ = I - SWAP = 2 P₋`, so `V V^* = P₋`;
* `complement_O`, `complement_E`: tracing out either output factor of `V2 E_ij V2ᵀ` gives
  `W2(E_ij)`, so `W` is its own complementary channel;
* `choi`: `Σ_ij E_ij ⊗ W2(E_ij) = I - SWAP`, so the Choi state of `W` is `P₋/3`;
and, over any commutative ring, `Winv(Y) = Tr(Y) I - 2 Yᵀ` satisfies `Winv (W2 Y) = 2Y` and
`W2 (Winv Y) = 2Y` (`inverse_left`, `inverse_right`), i.e. `W^{-1} = Winv`, with
`Winv(I) = I` (`inverse_fixes_identity`).
-/

namespace WernerHolevo

open Matrix

abbrev Q := Fin 3
abbrev QQ := Fin 3 × Fin 3

/-- The Levi-Civita symbol on `Fin 3`. -/
def eps (i j k : Fin 3) : ℤ :=
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1) then 1
  else if (i, j, k) = (0, 2, 1) ∨ (i, j, k) = (2, 1, 0) ∨ (i, j, k) = (1, 0, 2) then -1 else 0

/-- `√2 V`: rows indexed by `(j, k)` (output, environment), columns by the input `i`. -/
def V2 : Matrix QQ Q ℤ := Matrix.of fun jk i => eps i jk.1 jk.2

/-- The swap of the two qutrits. -/
def SWAP : Matrix QQ QQ ℤ := Matrix.of fun a b => if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0

/-- `2W(Y) = Tr(Y) I - Yᵀ`. -/
def W2 (Y : Matrix Q Q ℤ) : Matrix Q Q ℤ := Y.trace • (1 : Matrix Q Q ℤ) - Yᵀ

/-- The matrix unit `E_ij`. -/
def E (i j : Q) : Matrix Q Q ℤ := Matrix.of fun a b => if a = i ∧ b = j then 1 else 0

/-- Trace out the first (output) factor. -/
def trO (M : Matrix QQ QQ ℤ) : Matrix Q Q ℤ := Matrix.of fun b d => ∑ a : Q, M (a, b) (a, d)

/-- Trace out the second (environment) factor. -/
def trE (M : Matrix QQ QQ ℤ) : Matrix Q Q ℤ := Matrix.of fun a c => ∑ b : Q, M (a, b) (c, b)

theorem V2_isometry : V2ᵀ * V2 = 2 • (1 : Matrix Q Q ℤ) := by decide

theorem V2_proj : V2 * V2ᵀ = 1 - SWAP := by decide

theorem complement_O (i j : Q) : trO (V2 * E i j * V2ᵀ) = W2 (E i j) := by
  fin_cases i <;> fin_cases j <;> decide

theorem complement_E (i j : Q) : trE (V2 * E i j * V2ᵀ) = W2 (E i j) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The Choi matrix of `2W` is `I - SWAP`: `Σ_ij E_ij ⊗ 2W(E_ij)`. -/
def choi2 : Matrix QQ QQ ℤ := Matrix.of fun a b => W2 (E a.1 b.1) a.2 b.2

theorem choi : choi2 = 1 - SWAP := by decide

variable {R : Type*} [CommRing R]

/-- `2W` over a commutative ring. -/
def W2R (Y : Matrix Q Q R) : Matrix Q Q R := Y.trace • (1 : Matrix Q Q R) - Yᵀ

/-- The stated inverse `W^{-1}(Y) = Tr(Y) I - 2Yᵀ`. -/
def Winv (Y : Matrix Q Q R) : Matrix Q Q R := Y.trace • (1 : Matrix Q Q R) - (2 : R) • Yᵀ

theorem inverse_left (Y : Matrix Q Q R) : Winv (W2R Y) = (2 : R) • Y := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Winv, W2R, Matrix.trace, Fin.sum_univ_three] <;> ring

theorem inverse_right (Y : Matrix Q Q R) : W2R (Winv Y) = (2 : R) • Y := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Winv, W2R, Matrix.trace, Fin.sum_univ_three] <;> ring

theorem inverse_fixes_identity : Winv (1 : Matrix Q Q R) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Winv, Matrix.trace] <;> ring

end WernerHolevo

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms WernerHolevo.V2_isometry
#print axioms WernerHolevo.V2_proj
#print axioms WernerHolevo.complement_O
#print axioms WernerHolevo.complement_E
#print axioms WernerHolevo.choi
#print axioms WernerHolevo.inverse_left
#print axioms WernerHolevo.inverse_right
#print axioms WernerHolevo.inverse_fixes_identity
