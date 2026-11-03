import CircuitEnergy
import Mathlib.Data.Matrix.Block

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseShellBlocks

variable {s : Type} [Fintype s] [DecidableEq s]
    {a : s → Type} [∀ i, Fintype (a i)] [∀ i, DecidableEq (a i)]

theorem block_unitary (U : ∀ i, Mat (a i)) (hU : ∀ i, IsUnitary (U i)) :
    IsUnitary (blockDiagonal' U) := by
  constructor
  · rw [blockDiagonal'_conjTranspose,← blockDiagonal'_mul]
    simpa only [(funext fun i => (hU i).1)] using
      (blockDiagonal'_one : blockDiagonal' (fun i => (1 : Mat (a i)))=1)
  · rw [blockDiagonal'_conjTranspose,← blockDiagonal'_mul]
    simpa only [(funext fun i => (hU i).2)] using
      (blockDiagonal'_one : blockDiagonal' (fun i => (1 : Mat (a i)))=1)

theorem block_conserves (U : ∀ i, Mat (a i)) (hU : ∀ i, IsUnitary (U i)) (E : s → ℝ) :
    Conserves (blockDiagonal' U) (diagonal (fun i : Sigma a => (E i.1 : ℂ))) := by
  have hcomm : (blockDiagonal' U)*diagonal (fun i : Sigma a => (E i.1 : ℂ)) =
      diagonal (fun i : Sigma a => (E i.1 : ℂ))*(blockDiagonal' U) := by
    ext ⟨i,x⟩ ⟨j,y⟩
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases h : i=j
    · subst j
      exact mul_comm _ _
    · rw [blockDiagonal'_apply_ne U x y h]
      simp
  unfold Conserves
  rw [mul_assoc,← hcomm,← mul_assoc,(block_unitary U hU).1,one_mul]

/-- A finite direct sum of unitary energy-shell blocks remains conserving
in arbitrary physical coordinates. The fiber dimensions may vary. -/
theorem transport {b : Type} [Fintype b] [DecidableEq b]
    (e : b ≃ Sigma a) (U : ∀ i, Mat (a i)) (hU : ∀ i, IsUnitary (U i)) (E : s → ℝ) :
    IsUnitary ((blockDiagonal' U).submatrix e e) ∧
      Conserves ((blockDiagonal' U).submatrix e e)
        ((diagonal (fun i : Sigma a => (E i.1 : ℂ))).submatrix e e) :=
  ⟨unitary_submatrix e (block_unitary U hU),
    conserves_reindex e _ _ (block_conserves U hU E)⟩

end ScheduleLaw.Blueprint.PhaseShellBlocks
