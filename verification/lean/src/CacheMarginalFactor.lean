import CacheMarginalAccuracy
import FactoryCacheMarginal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheMarginalFactor
open History CacheFlaggedCircuit FactoryRegisterOutput CacheControllerReturn
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def pairSplit (F : Formation β τ q (n+1)) :
    ((Fin (n+1) → Fin d) × Fin F.hardware.c) ≃ Fin d × ((Fin n → Fin d) × Fin F.hardware.c) where
  toFun | (batch,c) => ((CacheBatchSplit.split n batch).1,(CacheBatchSplit.split n batch).2,c)
  invFun | (s,cache,c) => ((CacheBatchSplit.split n).symm (s,cache),c)
  left_inv z := by rcases z with ⟨batch,c⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨s,cache,c⟩; simp only [Equiv.apply_symm_apply]

theorem pair_evolve (F : Formation β τ q (n+1)) (U : Mat (Fin (n+1) → Fin d))
    (M : Mat ((Fin (n+1) → Fin d) × CacheFactoryBody.Rest F)) :
    marginal (FactoryCacheMarginal.pairView F) (evolve (U ⊗ₖ (1 : Mat (CacheFactoryBody.Rest F))) M)=
      evolve (U ⊗ₖ (1 : Mat (Fin F.hardware.c))) (marginal (FactoryCacheMarginal.pairView F) M) := by
  have hu : (U ⊗ₖ (1 : Mat (CacheFactoryBody.Rest F))).submatrix
      (FactoryCacheMarginal.pairView F).symm (FactoryCacheMarginal.pairView F).symm =
        (U ⊗ₖ (1 : Mat (Fin F.hardware.c))) ⊗ₖ (1 : Mat (FactoryCacheMarginal.Remaining F)) := by
    ext ⟨⟨b,c⟩,w,a⟩ ⟨⟨b',c'⟩,w',a'⟩
    simp only [submatrix_apply,FactoryCacheMarginal.pairView,Equiv.coe_fn_symm_mk,
      kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [marginal,← evolve_submatrix_equiv,hu,partialRight_evolve_kron_one]
  rfl

theorem tail_pair (F : Formation β τ q (n+1)) (A : Mat (Fin (n+1) → Fin d))
    (C : Mat (Fin F.hardware.c)) :
    partialLeft ((A ⊗ₖ C).submatrix (pairSplit F).symm (pairSplit F).symm)=
      partialLeft (A.submatrix (CacheBatchSplit.split n).symm (CacheBatchSplit.split n).symm) ⊗ₖ C := by
  ext ⟨cache,c⟩ ⟨cache',c'⟩
  simp only [partialLeft,submatrix_apply,pairSplit,Equiv.coe_fn_symm_mk,
    kroneckerMap_apply,Finset.sum_mul]

theorem sector (F : Formation β τ q (n+1)) (k : Fin (n+1)) (u v : Fin 2)
    (M : Mat ((Fin (n+1) → Fin d) × CacheFactoryBody.Rest F)) :
    marginal (wholeFrame F) (level (k,u,v) ⊗ₖ M)=
      (level k ⊗ₖ partialLeft ((marginal (FactoryCacheMarginal.pairView F) M).submatrix
        (pairSplit F).symm (pairSplit F).symm)).submatrix
          (Equiv.prodAssoc (Fin (n+1)) (Fin n → Fin d) (Fin F.hardware.c))
          (Equiv.prodAssoc (Fin (n+1)) (Fin n → Fin d) (Fin F.hardware.c)) := by
  letI : Nonempty (Fin d) := τ.toMState.nonempty
  letI : Nonempty (Fin F.hardware.w) := ⟨⟨0,F.hardware.w_pos⟩⟩
  letI : Nonempty (Fin F.aux) := ⟨⟨0,F.aux_pos⟩⟩
  rw [CacheBatchSplit.level_prod k (u,v)]
  ext ⟨⟨k0,cache⟩,c⟩ ⟨⟨k1,cache'⟩,c'⟩
  by_cases hk0 : k0=k <;> by_cases hk1 : k1=k <;>
    simp [marginal,wholeFrame,CacheBatchSplit.frame,partialRight,partialLeft,
      FactoryCacheMarginal.pairView,pairSplit,submatrix_apply,kroneckerMap_apply,
      level,pureMatrix,hk0,hk1,Fintype.sum_prod_type]

theorem ideal_sector (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    marginal (wholeFrame F) (CacheRareBranch.idealSector F j)=
      (level (CacheClockAdvance.step n j) ⊗ₖ
        (CacheBatchSplit.cacheSector τ q n (CacheClockAdvance.step n j)).matrix) ⊗ₖ
          F.hardware.controller.matrix := by
  have he : (CacheRareBranch.idealSector F j).submatrix (wholeFrame F).symm (wholeFrame F).symm =
      ((level (CacheClockAdvance.step n j) ⊗ₖ
        (CacheBatchSplit.cacheSector τ q n (CacheClockAdvance.step n j)).matrix) ⊗ₖ
          F.hardware.controller.matrix) ⊗ₖ (rest F).matrix := by
    ext ⟨⟨⟨k,cache⟩,c⟩,flags,b,w,a⟩ ⟨⟨⟨k',cache'⟩,c'⟩,flags',b',w',a'⟩
    simp only [CacheRareBranch.idealSector,CacheRareBranch.stock,wholeFrame,
      CacheBatchSplit.frame,rest,CacheFactoryBody.helper,submatrix_apply,
      Equiv.coe_fn_symm_mk,Equiv.coe_fn_mk,Equiv.apply_symm_apply,kroneckerMap_apply]
    ring
  rw [marginal,he,partialRight_kron,(rest F).normalized,one_smul]

theorem boundary (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef)
    (ω : Density (CacheFactoryBody.Batch d (n+1) × FactoryCacheMarginal.Remaining F))
    (hω : CacheFactoryBody.result F=(F.hardware.controller.matrix ⊗ₖ ω.matrix).submatrix
      (FactoryCacheMarginal.controllerView F) (FactoryCacheMarginal.controllerView F)) :
    marginal (wholeFrame F) (evolve (circuit F) (inputSector F 0))=
      (level (CacheClockAdvance.step n 0) ⊗ₖ CacheMarginalAccuracy.tail (n:=n) F.output) ⊗ₖ
        F.hardware.controller.matrix := by
  rw [CacheFlaggedCircuit.boundary F hβ hq]
  simp only [CacheClockAdvance.target,if_true]
  rw [sector,pair_evolve]
  change _= _
  rw [show marginal (FactoryCacheMarginal.pairView F) (CacheFactoryBody.result F)=
      F.output ⊗ₖ F.hardware.controller.matrix from FactoryCacheMarginal.pair_product F ω hω,
    CacheFlaggedCircuit.kron_evolve]
  have hid : evolve (1 : Mat (Fin F.hardware.c)) F.hardware.controller.matrix=F.hardware.controller.matrix := by
    simp [evolve]
  rw [hid,tail_pair]
  ext ⟨⟨k,cache⟩,c⟩ ⟨⟨k',cache'⟩,c'⟩
  simp only [submatrix_apply,Equiv.prodAssoc_apply,kroneckerMap_apply,CacheMarginalAccuracy.tail]
  ring

theorem ideal (F : Formation β τ q (n+1)) :
    marginal (wholeFrame F) (CacheRareBranch.ideal F)=(CacheControllerReturn.cache τ q n).matrix ⊗ₖ F.hardware.controller.matrix := by
  rw [marginal,CacheControllerReturn.ideal_product,partialRight_kron,(rest F).normalized,one_smul]
  rfl

theorem factor (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef)
    (ω : Density (CacheFactoryBody.Batch d (n+1) × FactoryCacheMarginal.Remaining F))
    (hω : CacheFactoryBody.result F=(F.hardware.controller.matrix ⊗ₖ ω.matrix).submatrix
      (FactoryCacheMarginal.controllerView F) (FactoryCacheMarginal.controllerView F)) :
    marginal (wholeFrame F) (CacheMixture.output F)=(CacheMarginalAccuracy.cache F).matrix ⊗ₖ
      F.hardware.controller.matrix := by
  have h := congrArg (marginal (wholeFrame F)) (CacheRareBranch.difference F)
  rw [CacheBatteryBudget.marginal_sub,ideal,CacheWorkState.marginal_smul,CacheBatteryBudget.marginal_sub,
    boundary F hβ hq ω hω,ideal_sector] at h
  have hk := CacheMarginalAccuracy.difference F hβ hq
  rw [CacheMarginalAccuracy.tail_target (τ:=τ) (q:=q) (n:=n)] at hk
  have he : marginal (wholeFrame F) (CacheMixture.output F)-(CacheControllerReturn.cache τ q n).matrix ⊗ₖ F.hardware.controller.matrix =
      ((CacheMarginalAccuracy.cache F).matrix-(CacheControllerReturn.cache τ q n).matrix) ⊗ₖ F.hardware.controller.matrix := by
    rw [h,hk]
    ext i j
    simp only [Matrix.smul_apply,Matrix.sub_apply,kroneckerMap_apply,Complex.real_smul]
    ring
  rw [CacheRareProduct.sub_kron] at he
  have hh := congrArg (fun M => M+(CacheControllerReturn.cache τ q n).matrix ⊗ₖ F.hardware.controller.matrix) he
  simpa only [sub_add_cancel] using hh

end ScheduleLaw.Blueprint.CacheMarginalFactor
