/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license; see LICENSE-APACHE-2.0.txt.
Authors: QuAIR Team

Lean 4.30 adaptation of the companion Lean-QIT snapshot's
QIT/States/Purification/GramFactorization.lean. The conclusion is expressed
directly with a matrix instead of importing the ReferenceIsometry bundle.
Namespace and imports adapted. Source hashes are recorded under logs/round6/.
-/
import PurificationExtension
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace ScheduleLaw.History

theorem gram_factor_isometry {a r₁ r₂ : Type}
    [Fintype a] [DecidableEq a] [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂] (A : Matrix a r₁ ℂ) (B : Matrix a r₂ ℂ)
    (hGram : A * Aᴴ = B * Bᴴ) (hcard : Fintype.card r₁ ≤ Fintype.card r₂) :
    ∃ V : Matrix r₂ r₁ ℂ, Vᴴ * V = 1 ∧ B = A * Vᵀ := by
  let T₁ : EuclideanSpace ℂ r₁ →ₗ[ℂ] EuclideanSpace ℂ a := A.toEuclideanLin
  let T₂ : EuclideanSpace ℂ r₂ →ₗ[ℂ] EuclideanSpace ℂ a := B.toEuclideanLin
  have hGramLin : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint := by
    dsimp [T₁,T₂]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B]
    simpa [Matrix.toEuclideanLin,Matrix.toLpLin_mul] using
      congrArg Matrix.toEuclideanLin hGram
  have hfin : Module.finrank ℂ (EuclideanSpace ℂ r₁) ≤
      Module.finrank ℂ (EuclideanSpace ℂ r₂) := by
    simpa [finrank_euclideanSpace] using hcard
  obtain ⟨U,hU⟩ := LinearMap.exists_isometry_apply_adjoint_of_comp_adjoint_eq hGramLin hfin
  have hAdj : U.toLinearMap.comp T₁.adjoint = T₂.adjoint := by
    apply _root_.LinearMap.ext
    intro y
    exact hU y
  have hFactor : T₂ = T₁.comp U.adjoint := by
    have h := congrArg _root_.LinearMap.adjoint hAdj
    simpa using h.symm
  let M : Matrix r₂ r₁ ℂ := Matrix.toEuclideanLin.symm U.toLinearMap
  have hMlin : M.toEuclideanLin = U.toLinearMap := by simp [M]
  have hMadj : Mᴴ.toEuclideanLin = U.adjoint := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hMlin]
  have hunitM : Mᴴ * M = 1 := by
    have hunitLin : Mᴴ.toEuclideanLin.comp M.toEuclideanLin =
        (_root_.LinearMap.id : EuclideanSpace ℂ r₁ →ₗ[ℂ] EuclideanSpace ℂ r₁) := by
      simp [hMlin,hMadj]
    apply Matrix.toEuclideanLin.injective
    simpa [Matrix.toEuclideanLin,Matrix.toLpLin_mul,Matrix.toLpLin_one] using hunitLin
  let V : Matrix r₂ r₁ ℂ := M.map star
  refine ⟨V,?_,?_⟩
  · ext i j
    have h := congrFun₂ hunitM j i
    simpa [V,Matrix.mul_apply,Matrix.conjTranspose,Matrix.one_apply,Matrix.map_apply,
      eq_comm,Finset.mul_sum,mul_comm] using h
  · apply Matrix.toEuclideanLin.injective
    have ht : B.toEuclideanLin = (A * Mᴴ).toEuclideanLin := by
      calc B.toEuclideanLin = A.toEuclideanLin.comp U.adjoint := hFactor
        _ = A.toEuclideanLin.comp Mᴴ.toEuclideanLin := by rw [hMadj]
        _ = (A * Mᴴ).toEuclideanLin := by rw [Matrix.toLpLin_mul]
    simpa [V,Matrix.conjTranspose,Matrix.transpose] using ht

end ScheduleLaw.History
