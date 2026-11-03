import AccessibleHistory
import Mathlib.Analysis.CStarAlgebra.Hom

/-! Operator-norm control and lawful correction time of the concrete
retained-body observable. No physical slack/link formula is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.History

@[reducible]
def matrixCStarStructure (a : Type) [Fintype a] [DecidableEq a] : CStarAlgebra (Mat a) where

def kronIdentityHom (a z : Type) [Fintype a] [DecidableEq a] [Fintype z] [DecidableEq z] :
    Mat a →⋆ₐ[ℂ] Mat (a × z) where
  toFun A := A ⊗ₖ 1
  map_zero' := by ext i j; simp
  map_one' := one_kronecker_one
  map_add' A B := add_kronecker A B 1
  map_mul' A B := by rw [← mul_kronecker_mul,one_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,
      smul_kronecker,one_kronecker_one]
  map_star' A := by
    change Aᴴ ⊗ₖ (1 : Mat z) = (A ⊗ₖ (1 : Mat z))ᴴ
    rw [conjTranspose_kronecker,conjTranspose_one]

theorem kronIdentityHom_injective {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] [Nonempty z] : Function.Injective (kronIdentityHom a z) := by
  intro A B h
  let k : z := Classical.choice inferInstance
  ext i j
  have ht := congrFun₂ h (i,k) (j,k)
  change A i j * (1 : Mat z) k k = B i j * (1 : Mat z) k k at ht
  simpa using ht

theorem kron_identity_opNorm {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] [Nonempty z] (A : Mat a) :
    ‖A ⊗ₖ (1 : Mat z)‖ = ‖A‖ := by
  letI := matrixCStarStructure a
  letI := matrixCStarStructure (a × z)
  exact NonUnitalStarAlgHom.norm_map (kronIdentityHom a z) kronIdentityHom_injective A

def matrixReindexStarEquiv {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) : Mat a ≃⋆ₐ[ℂ] Mat b where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_star' A := by ext i j; rfl
  map_smul' c A := by ext i j; rfl

theorem reindex_opNorm {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (A : Mat b) :
    ‖A.submatrix e e‖ = ‖A‖ := by
  letI := matrixCStarStructure a
  letI := matrixCStarStructure b
  exact NonUnitalStarAlgHom.norm_map (matrixReindexStarEquiv e.symm)
    (matrixReindexStarEquiv e.symm).injective A

theorem recorderHistoryEffect_norm {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (D : HermitianMat (TerminalSpace S h) ℂ) :
    ‖recorderHistoryEffect S h D‖ =
      (prefixDimension (lastInputBurst S h) : ℝ) * ‖D.mat‖ := by
  let b := lastInputBurst S h
  let p := stockPartition S (arrived S (recordTime b)) (released S (recordTime b))
  calc ‖recorderHistoryEffect S h D‖ =
      ‖((prefixDimension b : ℂ) • D.mat) ⊗ₖ
        (1 : Mat (Record S (arrived S (recordTime b))ᶜ (released S (recordTime b))ᶜ))‖ :=
        reindex_opNorm ((Recorder.stockFin S).symm.trans p) _
    _ = ‖(prefixDimension b : ℂ) • D.mat‖ := kron_identity_opNorm _
    _ = (prefixDimension b : ℝ) * ‖D.mat‖ := by rw [norm_smul]; simp

theorem recorderHistoryEffect_at_record {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) (D : HermitianMat (TerminalSpace S h) ℂ) :
    energy (recorderHistoryEffect S h D)
      (partialRight (run (Recorder.extension S) t (recordTime (lastInputBurst S h)))) =
      inner ℝ D (terminalTesterVector S h t : HermitianMat (TerminalSpace S h) ℂ) := by
  have ht := body_after_last S h t (2*S.visits+1) (recordTime_bound _)
  rw [← ht]
  exact recorderHistoryEffect_expectation S h t D

theorem positive_accessible_history_effect {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (L : terminalSpan S h →ₗ[ℝ] ℝ)
    (hL : ∀ A : terminalSpan S h, 0 ≤ (A : HermitianMat (TerminalSpace S h) ℂ) → 0 ≤ L A) :
    ∃ D : HermitianMat (TerminalSpace S h) ℂ,
      (recorderHistoryEffect S h D).PosSemidef ∧
      ‖recorderHistoryEffect S h D‖ ≤
        (prefixDimension (lastInputBurst S h) : ℝ) *
          (terminalInputDimension S h : ℝ) * L (terminalFlatVector S h) ∧
      ∀ r (t : Tester S r), energy (recorderHistoryEffect S h D)
        (partialRight (run (Recorder.extension S) t (recordTime (lastInputBurst S h)))) =
          L (terminalTesterVector S h t) := by
  obtain ⟨D,hD,hn,hpos,hev⟩ := positive_recorder_representative S h L hL
  refine ⟨D,hpos,?_,?_⟩
  · rw [recorderHistoryEffect_norm,mul_assoc]
    exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
  · intro r t
    rw [recorderHistoryEffect_at_record]
    have ht := hev r t
    rw [recorderHistoryEffect_expectation] at ht
    exact ht

end ScheduleLaw.History
