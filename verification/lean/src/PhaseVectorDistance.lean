import TraceMarginal
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder InnerProductSpace
namespace ScheduleLaw.Blueprint.PhaseVectorDistance

variable {a : Type} [Fintype a] [DecidableEq a]

abbrev vector (u : a → ℂ) : EuclideanSpace ℂ a := WithLp.toLp 2 u

theorem norm_unitary (U : Mat a) (hU : IsUnitary U) (u : a → ℂ) :
    ‖vector (U *ᵥ u)‖=‖vector u‖ := by
  have hi : inner ℂ (vector (U *ᵥ u)) (vector (U *ᵥ u))=inner ℂ (vector u) (vector u) := by
    simp only [vector,EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm (U *ᵥ u) (star (U *ᵥ u)),star_mulVec,dotProduct_mulVec,
      vecMul_vecMul,hU.1,vecMul_one,dotProduct_comm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),norm_sq_eq_re_inner (𝕜:=ℂ),hi]

theorem unitary_instances (U : Mat a) (D E : DecidableEq a)
    (h : @IsUnitary a _ D U) : @IsUnitary a _ E U := by
  have hh : D=E := Subsingleton.elim _ _
  cases hh
  exact h

def outer (u v : a → ℂ) : Mat a := vecMulVec u (star v)

theorem outer_bound (u v : a → ℂ) :
    Matrix.traceNorm (outer u v) ≤ ‖vector u‖*‖vector v‖ := by
  obtain ⟨W,hW⟩ := (Matrix.traceNorm_eq_max_re_tr_U (outer u v)).1
  have ht : ((W : Mat a)*outer u v).trace=
      inner ℂ (vector v) (vector ((W : Mat a) *ᵥ u)) := by
    rw [outer,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
    rfl
  rw [← hW,ht]
  calc (inner ℂ (vector v) (vector ((W : Mat a) *ᵥ u))).re
      ≤ ‖inner ℂ (vector v) (vector ((W : Mat a) *ᵥ u))‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
       _ ≤ ‖vector v‖*‖vector ((W : Mat a) *ᵥ u)‖ := norm_inner_le_norm _ _
       _ = ‖vector u‖*‖vector v‖ := by
         rw [norm_unitary _ (unitary_instances _ _ _ (TraceMarginal.unitary_ok W)),mul_comm]

/-- The original half-trace distance is bounded by the Euclidean distance
of normalized purification vectors, uniformly in the reference dimension. -/
theorem pure_distance (u v : a → ℂ) (hu : ‖vector u‖=1) (hv : ‖vector v‖=1) :
    traceDistance (pureMatrix u) (pureMatrix v) ≤ ‖vector u-vector v‖ := by
  have hd : pureMatrix u-pureMatrix v=outer (u-v) u+outer v (u-v) := by
    ext i j
    simp only [pureMatrix,outer,Matrix.vecMulVec_apply,Matrix.sub_apply,Matrix.add_apply,
      Pi.sub_apply,Pi.star_apply,star_sub]
    ring
  have hn : vector (u-v)=vector u-vector v := rfl
  have h := (Matrix.traceNorm_add_le (outer (u-v) u) (outer v (u-v))).trans
    (add_le_add (outer_bound (u-v) u) (outer_bound v (u-v)))
  rw [hu,hv,hn,mul_one,one_mul] at h
  rw [traceDistance,ClassicalFlag.traceNorm_eq_library,hd]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr (by linarith)

theorem normalized_sum (u : a → ℂ) (hu : ‖vector u‖=1) :
    (∑ i,Complex.normSq (u i))=1 := by
  have hs := EuclideanSpace.norm_sq_eq (vector u)
  rw [hu,one_pow] at hs
  simpa only [vector,PiLp.toLp_apply,Complex.normSq_eq_norm_sq] using hs.symm

theorem pure_entropy (u : a → ℂ) (hu : ‖vector u‖=1) : entropy (pureMatrix u)=0 := by
  let ψ : Ket a := ⟨u,by
    simpa only [Complex.normSq_eq_norm_sq] using normalized_sum u hu⟩
  let ρ : Density a := ⟨pureMatrix u,pureMatrix_positive u,by
    rw [pureMatrix_trace,normalized_sum u hu]
    norm_num⟩
  have he : ρ.toMState=MState.pure ψ := by
    ext i j
    rfl
  change entropy ρ.matrix=0
  rw [density_entropy_eq_library,he,Sᵥₙ_of_pure_zero]

end ScheduleLaw.Blueprint.PhaseVectorDistance
