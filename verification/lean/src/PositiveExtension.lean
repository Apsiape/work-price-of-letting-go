import ConeConsequences
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Finite-dimensional positive-functional extension on any Hermitian
subspace containing the identity. All order and duality facts are proved;
CombRealization is not used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace RealInnerProductSpace
namespace ScheduleLaw.History

def hermitianPositiveCone (a : Type) [Fintype a] : ConvexCone ℝ (HermitianMat a ℂ) where
  carrier := {A | 0 ≤ A}
  smul_mem' c hc A hA := by
    change 0 ≤ c • A
    exact smul_nonneg hc.le hA
  add_mem' {A} hA {B} hB := by
    change 0 ≤ A + B
    exact add_nonneg hA hB

theorem positive_norm_le_trace {a : Type} [Fintype a] [DecidableEq a]
    (A : HermitianMat a ℂ) (hA : 0 ≤ A) : ‖A‖ ≤ A.trace := by
  have ht : 0 ≤ A.trace := by
    rw [← HermitianMat.inner_one]
    exact HermitianMat.inner_ge_zero hA (HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one)
  have hs := HermitianMat.inner_le_mul_trace hA hA
  rw [real_inner_self_eq_norm_sq] at hs
  exact (sq_le_sq₀ (norm_nonneg _) ht).mp (by nlinarith)

/-- A positive linear functional on an identity-containing subspace has a
positive Hermitian representative on the full finite history space. Its
trace and norm are controlled by its value on the identity. -/
theorem positive_functional_representative {a : Type} [Fintype a] [DecidableEq a]
    (V : Submodule ℝ (HermitianMat a ℂ)) (h1 : (1 : HermitianMat a ℂ) ∈ V)
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ A : V, 0 ≤ (A : HermitianMat a ℂ) → 0 ≤ L A) :
    ∃ D : HermitianMat a ℂ, 0 ≤ D ∧
      (∀ A : V, ⟪D,(A : HermitianMat a ℂ)⟫_ℝ = L A) ∧
      D.trace = L ⟨1,h1⟩ ∧ ‖D‖ ≤ D.trace := by
  let f : HermitianMat a ℂ →ₗ.[ℝ] ℝ := ⟨V,L⟩
  have hdense : ∀ y : HermitianMat a ℂ, ∃ x : f.domain,
      (x : HermitianMat a ℂ) + y ∈ hermitianPositiveCone a := by
    intro y
    refine ⟨⟨‖y‖ • 1,V.smul_mem _ h1⟩,?_⟩
    have hy : -y ≤ ‖y‖ • (1 : HermitianMat a ℂ) := by
      simpa only [norm_neg] using HermitianMat.lt_smul_of_norm_lt (A := -y) le_rfl
    simpa only [hermitianPositiveCone,ConvexCone.mem_mk,Set.mem_setOf_eq,sub_neg_eq_add]
      using sub_nonneg.mpr hy
  obtain ⟨g,hg,hpos⟩ := riesz_extension (hermitianPositiveCone a) f (fun x hx => hL x (by simpa only [hermitianPositiveCone,ConvexCone.mem_mk,Set.mem_setOf_eq] using hx)) hdense
  let gC : HermitianMat a ℂ →L[ℝ] ℝ :=
    ⟨g,g.continuous_of_finiteDimensional⟩
  let D := (InnerProductSpace.toDual ℝ (HermitianMat a ℂ)).symm gC
  have hev (A : HermitianMat a ℂ) : ⟪D,A⟫_ℝ = g A :=
    InnerProductSpace.toDual_symm_apply
  have hD : 0 ≤ D := (HermitianMat.nonneg_iff_inner_nonneg D).mpr
    (fun A hA => (hev A).symm ▸ hpos A (by simpa only [hermitianPositiveCone,ConvexCone.mem_mk,Set.mem_setOf_eq] using hA))
  refine ⟨D,hD,fun A => (hev A).trans (hg A),?_,positive_norm_le_trace D hD⟩
  rw [← HermitianMat.inner_one,hev]
  exact hg ⟨1,h1⟩

end ScheduleLaw.History
