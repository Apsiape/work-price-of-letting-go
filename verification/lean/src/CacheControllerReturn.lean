import CacheRareProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheControllerReturn
open History CacheFlaggedCircuit

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}
abbrev Controller (F : Formation β τ q (n+1)) :=
  (Fin (n+1) × (Fin n → Fin d)) × Fin F.hardware.c
abbrev Rest (F : Formation β τ q (n+1)) :=
  (Fin 2 × Fin 2) × (Fin d × (Fin F.hardware.w × Fin F.aux))

def wholeFrame (F : Formation β τ q (n+1)) : Physical F ≃ Controller F × Rest F where
  toFun z := let u := CacheBatchSplit.frame F z
             ((u.1,u.2.2.2.1),u.2.1,u.2.2.1,u.2.2.2.2)
  invFun | ((cache,c),flags,b,w,a) => (CacheBatchSplit.frame F).symm (cache,flags,b,c,w,a)
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨cache,c⟩,flags,b,w,a⟩; simp only [Equiv.apply_symm_apply]

def cache (τ q : Density (Fin d)) (n : ℕ) : Density (Fin (n+1) × (Fin n → Fin d)) :=
  ⟨cacheState τ q (n+1),(cache_density τ q (n+1) (Nat.succ_pos n)).1,
    (cache_density τ q (n+1) (Nat.succ_pos n)).2⟩

def controller (F : Formation β τ q (n+1)) : Density (Controller F) :=
  CacheRareProduct.tensorDensity (cache τ q n) F.hardware.controller

def rest (F : Formation β τ q (n+1)) : Density (Rest F) := by
  letI : Nonempty (Fin F.aux) := ⟨⟨0,F.aux_pos⟩⟩
  refine ⟨level ((1 : Fin 2),(0 : Fin 2)) ⊗ₖ
    (τ.matrix ⊗ₖ (pureMatrix (fun j => if j=F.hardware.initialLevel then 1 else 0) ⊗ₖ
      gibbs β F.auxiliaryHamiltonian)),?_,?_⟩
  · exact (pureMatrix_positive _).kronecker
      (τ.positive.kronecker ((pureMatrix_positive _).kronecker (gibbs_positive _ _)))
  · simp only [trace_kronecker,τ.normalized,gibbs_trace,mul_one,one_mul,level]
    rw [pureMatrix_trace,pureMatrix_trace]
    simp

def reshaped (F : Formation β τ q (n+1)) : Mat (Controller F × Rest F) :=
  (CacheMixture.output F).submatrix (wholeFrame F).symm (wholeFrame F).symm

theorem ideal_product (F : Formation β τ q (n+1)) :
    (CacheRareBranch.ideal F).submatrix (wholeFrame F).symm (wholeFrame F).symm =
      (controller F).matrix ⊗ₖ (rest F).matrix := by
  ext ⟨⟨cache,c⟩,flags,b,w,a⟩ ⟨⟨cache',c'⟩,flags',b',w',a'⟩
  have h := congrArg (fun M => M (cache,flags,b,c,w,a) (cache',flags',b',c',w',a'))
    (CacheRareBranch.ideal_product F)
  simp only [submatrix_apply,kroneckerMap_apply,CacheRareBranch.stock,CacheFactoryBody.helper] at h
  simp only [submatrix_apply,wholeFrame,Equiv.coe_fn_symm_mk]
  rw [h]
  simp only [controller,ScheduleLaw.Blueprint.CacheControllerReturn.cache,CacheRareProduct.tensorDensity,rest,kroneckerMap_apply]
  ring

def actualBoundary (F : Formation β τ q (n+1)) : Density (Controller F × Rest F) :=
  ⟨(evolve (circuit F) (inputSector F 0)).submatrix (wholeFrame F).symm (wholeFrame F).symm,
    (CacheRareBranch.actual_sector_density F 0).1.submatrix _,by
      rw [submatrix_trace_equiv]; exact (CacheRareBranch.actual_sector_density F 0).2⟩

def idealBoundary (F : Formation β τ q (n+1)) : Density (Controller F × Rest F) :=
  ⟨(CacheRareBranch.idealSector F 0).submatrix (wholeFrame F).symm (wholeFrame F).symm,
    (CacheRareBranch.ideal_sector_density F 0).1.submatrix _,by
      rw [submatrix_trace_equiv]; exact (CacheRareBranch.ideal_sector_density F 0).2⟩

theorem difference (F : Formation β τ q (n+1)) :
    reshaped F-(controller F).matrix ⊗ₖ (rest F).matrix =
      ((n+1 : ℝ)⁻¹) • ((actualBoundary F).matrix-(idealBoundary F).matrix) := by
  rw [← ideal_product F]
  ext i j
  have h := congrArg (fun M => M ((wholeFrame F).symm i) ((wholeFrame F).symm j))
    (CacheRareBranch.difference F)
  simpa only [reshaped,actualBoundary,idealBoundary,submatrix_apply,Matrix.sub_apply,Matrix.smul_apply] using h

/-- The actual pre-service cache circuit returns the whole invested
clock/cache/factory controller jointly with every retained physical register. -/
theorem whole_rest (F : Formation β τ q (n+1)) :
    traceDistance (reshaped F) ((controller F).matrix ⊗ₖ partialLeft (reshaped F)) ≤ 2/(n+1 : ℝ) := by
  simpa only [div_eq_mul_inv] using CacheRareProduct.whole_rest (controller F) (rest F)
    (reshaped F) (actualBoundary F) (idealBoundary F) ((n+1 : ℝ)⁻¹) (by positivity) (difference F)

end ScheduleLaw.Blueprint.CacheControllerReturn
