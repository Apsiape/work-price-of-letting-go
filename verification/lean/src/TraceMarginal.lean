import CacheRareProduct
import FiniteTensorMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.TraceMarginal
open History
variable {a b : Type} [Fintype a] [Fintype b]

theorem right_sub (A B : Mat (a × b)) :
    partialRight (A-B)=partialRight A-partialRight B := by
  classical
  ext i j
  simp only [partialRight,Matrix.sub_apply,Finset.sum_sub_distrib]

theorem right_smul (A : Mat (a × b)) (p : ℝ) :
    partialRight (p • A)=p • partialRight A := by
  classical
  ext i j
  simp only [partialRight,Matrix.smul_apply,Finset.smul_sum]

theorem adjoint_trace (U : Mat a) (A : Mat (a × b)) :
    (U * partialRight A).trace=((U ⊗ₖ (1 : Mat b))*A).trace := by
  classical
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,partialRight,kroneckerMap_apply,Fintype.sum_prod_type,
    Matrix.one_apply,Finset.mul_sum,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

def asUnitary (U : Mat a) (hU : IsUnitary U) : Matrix.unitaryGroup a ℂ := by
  refine ⟨U,?_⟩
  constructor
  · change Uᴴ*U=1
    exact hU.1
  · change U*Uᴴ=1
    exact hU.2

theorem unitary_ok (U : Matrix.unitaryGroup a ℂ) : IsUnitary (U : Mat a) := by
  constructor
  · exact Unitary.coe_star_mul_self U
  · exact Unitary.coe_mul_star_self U

theorem right_norm (A : Mat (a × b)) :
    Matrix.traceNorm (partialRight A) ≤ Matrix.traceNorm A := by
  classical
  letI : DecidableEq (a × b) := Classical.decEq _
  obtain ⟨U,hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (partialRight A)).1
  have hi : IsUnitary (1 : Mat b) := by constructor <;> simp
  have hu := unitary_kron (U:=(U : Mat a)) (V:=(1 : Mat b)) (unitary_ok U) hi
  let V : Matrix.unitaryGroup (a × b) ℂ := ⟨(U : Mat a) ⊗ₖ (1 : Mat b),by
    constructor
    · ext i j
      have hh := congrFun (congrFun hu.1 i) j
      by_cases hij : i=j <;> simpa [Matrix.one_apply,hij,Matrix.conjTranspose_kronecker] using hh
    · ext i j
      have hh := congrFun (congrFun hu.2 i) j
      by_cases hij : i=j <;> simpa [Matrix.one_apply,hij,Matrix.conjTranspose_kronecker] using hh⟩
  have h := (Matrix.traceNorm_eq_max_re_tr_U A).2
    (show ((V : Mat (a × b))*A).trace.re ∈
      {x : ℝ | ∃ W : Matrix.unitaryGroup (a × b) ℂ, ((W : Mat (a × b))*A).trace.re=x}
        from ⟨V,rfl⟩)
  rw [← hU,adjoint_trace]
  exact h

theorem right_distance [DecidableEq a] [DecidableEq b] (A B : Mat (a × b)) :
    traceDistance (partialRight A) (partialRight B) ≤ traceDistance A B := by
  classical
  unfold traceDistance
  rw [ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library,← right_sub]
  exact div_le_div_of_nonneg_right (right_norm (A-B)) (by norm_num)

theorem reindex_norm_le (e : a ≃ b) (A : Mat b) :
    Matrix.traceNorm (A.submatrix e e) ≤ Matrix.traceNorm A := by
  classical
  obtain ⟨U,hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (A.submatrix e e)).1
  let V : Matrix.unitaryGroup b ℂ := asUnitary _ (unitary_submatrix e.symm (unitary_ok U))
  have he : (((V : Mat b)*A).trace)=((U : Mat a)*A.submatrix e e).trace := by
    rw [← submatrix_trace_equiv e ((V : Mat b)*A),
      ← submatrix_mul_equiv (V : Mat b) A e e e]
    simp only [V,asUnitary,submatrix_submatrix,Equiv.symm_comp_self,submatrix_id_id]
  rw [← hU,← he]
  exact (Matrix.traceNorm_eq_max_re_tr_U A).2 ⟨V,rfl⟩

theorem reindex_norm (e : a ≃ b) (A : Mat b) :
    Matrix.traceNorm (A.submatrix e e)=Matrix.traceNorm A := by
  classical
  apply le_antisymm (reindex_norm_le e A)
  simpa only [submatrix_submatrix,Equiv.self_comp_symm,submatrix_id_id] using
    reindex_norm_le e.symm (A.submatrix e e)

theorem reindex_distance [DecidableEq a] [DecidableEq b] (e : a ≃ b) (A B : Mat b) :
    traceDistance (A.submatrix e e) (B.submatrix e e)=traceDistance A B := by
  classical
  unfold traceDistance
  rw [ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library]
  change Matrix.traceNorm ((A-B).submatrix e e)/2=Matrix.traceNorm (A-B)/2
  rw [reindex_norm]

theorem left_distance [DecidableEq a] [DecidableEq b] (A B : Mat (a × b)) :
    traceDistance (partialLeft A) (partialLeft B) ≤ traceDistance A B := by
  rw [partialLeft_swap,partialLeft_swap]
  exact (right_distance _ _).trans_eq (reindex_distance (Equiv.prodComm b a) A B)

theorem weighted_distance [DecidableEq a] (X Y A B : Mat a) (p : ℝ) (hp : 0≤p)
    (h : X-Y=p • (A-B)) : traceDistance X Y=p*traceDistance A B := by
  classical
  have he : p • (A-B)=(p : ℂ) • (A-B) := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  unfold traceDistance
  rw [h,he,ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library,
    Matrix.traceNorm_smul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  ring

def flagEmbedding [DecidableEq a] [DecidableEq b] (k : a) : Matrix (a × b) b ℂ := fun x j =>
  if x.1=k then if x.2=j then 1 else 0 else 0

theorem flag_isometry [DecidableEq a] [DecidableEq b] (k : a) : (flagEmbedding (b:=b) k).Isometry := by
  have he : flagEmbedding (b:=b) k=
      (1 : Mat (a × b)).submatrix id (fun j => (k,j)) := by
    ext ⟨x,i⟩ j
    by_cases hx : x=k <;> by_cases hi : i=j <;> simp [flagEmbedding,Matrix.one_apply,hx,hi]
  rw [he]
  exact Matrix.submatrix_one_id_right_isometry (fun i j h => (Prod.mk.inj h).2)

theorem flag_conjugation [DecidableEq a] [DecidableEq b] (k : a) (A : Mat b) :
    flagEmbedding (b:=b) k*A*(flagEmbedding (b:=b) k)ᴴ=CacheFlaggedCircuit.level k ⊗ₖ A := by
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases hx : x=k <;> by_cases hy : y=k <;>
    simp [Matrix.mul_apply,flagEmbedding,conjTranspose_apply,CacheFlaggedCircuit.level,
      pureMatrix,kroneckerMap_apply,hx,hy]

theorem flag_norm [DecidableEq a] [DecidableEq b] (k : a) (A : Mat b) :
    Matrix.traceNorm (CacheFlaggedCircuit.level k ⊗ₖ A)=Matrix.traceNorm A := by
  have hi : @Matrix.Isometry (a × b) b ℂ (inferInstance) (Classical.decEq b)
      (inferInstance) (inferInstance) (flagEmbedding (b:=b) k) := by
    ext i j
    have hh := congrFun (congrFun (flag_isometry (b:=b) k) i) j
    by_cases hij : i=j <;> simpa [Matrix.one_apply,hij] using hh
  rw [← flag_conjugation]
  exact (Matrix.traceNorm_isometry_right hi).trans (Matrix.traceNorm_isometry_left hi)

theorem flag_distance [DecidableEq a] [DecidableEq b] (k : a) (A B : Mat b) :
    traceDistance (CacheFlaggedCircuit.level k ⊗ₖ A)
      (CacheFlaggedCircuit.level k ⊗ₖ B)=traceDistance A B := by
  unfold traceDistance
  rw [← CacheRareProduct.kron_sub,ClassicalFlag.traceNorm_eq_library,
    ClassicalFlag.traceNorm_eq_library,flag_norm]

end ScheduleLaw.Blueprint.TraceMarginal
