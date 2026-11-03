import PhaseVectorDistance

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhasePureTensor
open PhaseVectorDistance
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def embedding (v : a → ℂ) : Matrix (a × b) b ℂ := fun x j =>
  v x.1*(if x.2=j then 1 else 0)

theorem isometry (v : a → ℂ) (hv : ‖vector v‖=1) : (embedding (b:=b) v).Isometry := by
  have hs : (∑ x,v x*star (v x))=(1 : ℂ) := by
    have hn : (pureMatrix v).trace=1 := by
      rw [pureMatrix_trace,normalized_sum v hv]
      norm_num
    exact hn
  have hs' : (∑ x,star (v x)*v x)=(1 : ℂ) := by
    simpa only [mul_comm] using hs
  ext i j
  by_cases hij : i=j
  · subst j
    simpa [Matrix.mul_apply,conjTranspose_apply,embedding,Fintype.sum_prod_type,
      Matrix.one_apply,star_mul,mul_assoc,ite_mul,mul_ite] using hs'
  · simp [Matrix.mul_apply,conjTranspose_apply,embedding,Fintype.sum_prod_type,
      Matrix.one_apply,star_mul,mul_assoc,ite_mul,mul_ite,hij,eq_comm,apply_ite]

theorem conjugation (v : a → ℂ) (A : Mat b) :
    embedding (b:=b) v*A*(embedding (b:=b) v)ᴴ=pureMatrix v ⊗ₖ A := by
  ext ⟨x,i⟩ ⟨y,j⟩
  simp [Matrix.mul_apply,embedding,conjTranspose_apply,pureMatrix,kroneckerMap_apply,
    star_mul,ite_mul,mul_ite,mul_assoc,mul_comm,mul_left_comm,apply_ite,eq_comm]

theorem trace_norm (v : a → ℂ) (hv : ‖vector v‖=1) (A : Mat b) :
    Matrix.traceNorm (pureMatrix v ⊗ₖ A)=Matrix.traceNorm A := by
  have hi : @Matrix.Isometry (a × b) b ℂ (inferInstance) (Classical.decEq b)
      (inferInstance) (inferInstance) (embedding (b:=b) v) := by
    ext i j
    have hh := congrFun (congrFun (isometry (b:=b) v hv) i) j
    by_cases hij : i=j <;> simpa [Matrix.one_apply,hij] using hh
  rw [← conjugation]
  exact (Matrix.traceNorm_isometry_right hi).trans (Matrix.traceNorm_isometry_left hi)

theorem distance (v : a → ℂ) (hv : ‖vector v‖=1) (A B : Mat b) :
    traceDistance (pureMatrix v ⊗ₖ A) (pureMatrix v ⊗ₖ B)=traceDistance A B := by
  unfold traceDistance
  rw [← CacheRareProduct.kron_sub,ClassicalFlag.traceNorm_eq_library,
    ClassicalFlag.traceNorm_eq_library,trace_norm v hv]

end ScheduleLaw.Blueprint.PhasePureTensor
