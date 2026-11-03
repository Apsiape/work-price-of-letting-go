import SupportTiles
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.SupportBasis

/-- Joint energy/support coordinates for one commuting pair. The source and
 target supports will use separate applications of this theorem. -/
theorem joint_basis {d : ℕ} (H P : Mat (Fin d)) (hH : H.IsHermitian)
    (hP : P.IsHermitian) (hHP : H*P=P*H) :
    ∃ (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (E F : Fin d → ℝ),
      (∀ i, H*ᵥ ⇑(b i) = (E i : ℂ) • ⇑(b i)) ∧
      (∀ i, P*ᵥ ⇑(b i) = (F i : ℂ) • ⇑(b i)) := by
  classical
  let A := Matrix.toEuclideanLin H
  let B := Matrix.toEuclideanLin P
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hB : B.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP
  have hc : Commute A B := by
    ext v i
    change (H*ᵥ (P*ᵥ ⇑v)) i = (P*ᵥ (H*ᵥ ⇑v)) i
    rw [mulVec_mulVec,mulVec_mulVec,hHP]
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := by simp only [finrank_euclideanSpace,Fintype.card_fin]
  let J := Module.End.Eigenvalues B × Module.End.Eigenvalues A
  let V (z : J) := Module.End.eigenspace A z.2 ⊓ Module.End.eigenspace B z.1
  let incl : J → ℂ × ℂ := fun z => (z.1,z.2)
  have hincl : Function.Injective incl := by
    intro x y h
    apply Prod.ext
    · apply Subtype.ext; exact congrArg Prod.fst h
    · apply Subtype.ext; exact congrArg Prod.snd h
  have ho : OrthogonalFamily ℂ (fun z : J => V z) (fun z => (V z).subtypeₗᵢ) :=
    (hA.orthogonalFamily_eigenspace_inf_eigenspace hB).comp (f := incl) hincl
  have hsup : (⨆ z : J, V z) = ⊤ := by
    apply le_antisymm le_top
    rw [← hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB hc]
    refine iSup_le (fun μ => iSup_le (fun ν => ?_))
    by_cases hμ : Module.End.eigenspace A μ = ⊥
    · simp [hμ]
    by_cases hν : Module.End.eigenspace B ν = ⊥
    · simp [hν]
    exact le_iSup_of_le ((⟨ν,hν⟩,⟨μ,hμ⟩) : J) le_rfl
  have hi : DirectSum.IsInternal V := ho.isInternal_iff.mpr (by rw [hsup,Submodule.top_orthogonal_eq_bot])
  obtain ⟨b,lab,hsub⟩ : ∃ (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
      (lab : Fin d → J), ∀ i, b i ∈ V (lab i) :=
    ⟨hi.subordinateOrthonormalBasis hn ho,fun i => hi.subordinateOrthonormalBasisIndex hn i ho,
      fun i => hi.subordinateOrthonormalBasis_subordinate hn i ho⟩
  let label (i : Fin d) : ℂ × ℂ := incl (lab i)
  have hb (i : Fin d) : b i ∈
      Module.End.eigenspace A (label i).2 ⊓ Module.End.eigenspace B (label i).1 := hsub i
  have hrealA (i : Fin d) : (((label i).2.re : ℝ) : ℂ) = (label i).2 := by
    exact RCLike.conj_eq_iff_re.mp (hA.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨(hb i).1,b.toBasis.ne_zero i⟩))
  have hrealB (i : Fin d) : (((label i).1.re : ℝ) : ℂ) = (label i).1 := by
    exact RCLike.conj_eq_iff_re.mp (hB.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨(hb i).2,b.toBasis.ne_zero i⟩))
  refine ⟨b,fun i => (label i).2.re,fun i => (label i).1.re,?_,?_⟩
  · intro i
    rw [hrealA]
    exact congrArg (fun v : EuclideanSpace ℂ (Fin d) => ⇑v)
      (Module.End.mem_eigenspace_iff.mp (hb i).1)
  · intro i
    rw [hrealB]
    exact congrArg (fun v : EuclideanSpace ℂ (Fin d) => ⇑v)
      (Module.End.mem_eigenspace_iff.mp (hb i).2)

/-- Convert an actual orthonormal eigenbasis to the full square matrix. -/
theorem basis_diagonal {d : ℕ} (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (A : Mat (Fin d)) (e : Fin d → ℝ)
    (hA : ∀ j, A*ᵥ ⇑(b j) = (e j : ℂ) • ⇑(b j)) :
    let U := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis
    IsUnitary U ∧ A = evolve U (diagonal (fun j => (e j : ℂ))) := by
  classical
  dsimp only
  let U := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis
  have hU : IsUnitary U := (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hcol (i j : Fin d) : U i j = b j i := rfl
  have hm : A*U=U*diagonal (fun j => (e j : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    have h := congrArg (fun v : Fin d → ℂ => v i) (hA j)
    change (∑ k, A i k * b j k) = (e j : ℂ)*b j i at h
    simpa only [hcol,mul_comm] using h
  refine ⟨hU,?_⟩
  calc A = A*(U*Uᴴ) := by rw [hU.2,mul_one]
       _ = evolve U (diagonal (fun j => (e j : ℂ))) := by
         rw [← mul_assoc,hm]
         rfl

end ScheduleLaw.Blueprint.SupportBasis
