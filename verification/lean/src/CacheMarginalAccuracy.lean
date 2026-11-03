import TraceMarginal
import CacheBatteryBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheMarginalAccuracy
open History CacheFlaggedCircuit CacheBatchSplit FactoryRegisterOutput
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def tail (A : Mat (Fin (n+1) → Fin d)) : Mat (Fin n → Fin d) :=
  partialLeft ((evolve ((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ) A).submatrix
    (split n).symm (split n).symm)

def cache (F : Formation β τ q (n+1)) : Density (Fin (n+1) × (Fin n → Fin d)) :=
  ⟨marginal (frame F) (CacheMixture.output F),
    partialRight_positive ((CacheMixture.input_density F).1.mul_mul_conjTranspose_same _ |>.submatrix _),by
      rw [marginal,partialRight_trace,submatrix_trace_equiv,CacheMixture.output,
        evolve_trace _ _ (circuit_unitary F)]
      exact (CacheMixture.input_density F).2⟩

theorem stock_trace (F : Formation β τ q (n+1)) : (CacheRareBranch.stock F).trace=1 := by
  simp only [CacheRareBranch.stock,trace_kronecker,τ.normalized,
    (CacheMixture.helper_density F).2,one_mul,mul_one,level]
  rw [pureMatrix_trace]
  simp

theorem ideal (F : Formation β τ q (n+1)) :
    marginal (frame F) (CacheRareBranch.ideal F)=cacheState τ q (n+1) := by
  rw [marginal,CacheRareBranch.ideal_product,partialRight_kron,stock_trace,one_smul]

theorem ideal_boundary (F : Formation β τ q (n+1)) :
    marginal (frame F) (CacheRareBranch.idealSector F 0)=
      level (CacheClockAdvance.step n 0) ⊗ₖ (cacheSector τ q n (CacheClockAdvance.step n 0)).matrix := by
  rw [marginal,CacheRareBranch.idealSector]
  simp only [submatrix_submatrix,Equiv.self_comp_symm,submatrix_id_id]
  rw [partialRight_kron,stock_trace,one_smul]

theorem sector (F : Formation β τ q (n+1)) (k : Fin (n+1)) (u v : Fin 2)
    (M : Mat ((Fin (n+1) → Fin d) × CacheFactoryBody.Rest F)) :
    marginal (frame F) (level (k,u,v) ⊗ₖ M)=
      level k ⊗ₖ partialLeft ((partialRight M).submatrix (split n).symm (split n).symm) := by
  letI : Nonempty (Fin d) := τ.toMState.nonempty
  letI : Nonempty (Fin F.hardware.c) := ⟨⟨0,F.hardware.c_pos⟩⟩
  letI : Nonempty (Fin F.hardware.w) := ⟨⟨0,F.hardware.w_pos⟩⟩
  letI : Nonempty (Fin F.aux) := ⟨⟨0,F.aux_pos⟩⟩
  rw [level_prod k (u,v)]
  ext ⟨k0,c0⟩ ⟨k1,c1⟩
  by_cases hk0 : k0=k <;> by_cases hk1 : k1=k <;>
    simp [marginal,frame,partialRight,partialLeft,submatrix_apply,
      kroneckerMap_apply,level,pureMatrix,hk0,hk1,Fintype.sum_prod_type]

theorem boundary (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    marginal (frame F) (evolve (circuit F) (inputSector F 0))=
      level (CacheClockAdvance.step n 0) ⊗ₖ tail (n:=n) F.output := by
  rw [CacheFlaggedCircuit.boundary F hβ hq]
  simp only [CacheClockAdvance.target,if_true]
  rw [sector,partialRight_evolve_kron_one,CacheFactoryBody.output]
  rfl

theorem tail_distance (A B : Mat (Fin (n+1) → Fin d)) :
    traceDistance (tail (n:=n) A) (tail (n:=n) B) ≤ traceDistance A B := by
  unfold tail
  exact (TraceMarginal.left_distance _ _).trans
    ((TraceMarginal.reindex_distance (split n).symm _ _).le.trans_eq
      (FiniteResidue.traceDistance_unitary _ A B (Recorder.permutation_unitary _)))

theorem tail_target :
    tail (n:=n) (tensorPower τ.matrix (n+1))=(cacheSector τ q n (CacheClockAdvance.step n 0)).matrix := by
  have hr : evolve ((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ)
      (tensorPower τ.matrix (n+1))=tensorPower τ.matrix (n+1) := by
    change evolve _ (W2.tensorFamily (fun _ : Fin (n+1) => τ))=W2.tensorFamily (fun _ => τ)
    rw [CacheCellShift.tensor_state]
  unfold tail
  rw [hr]
  change partialLeft ((W2.tensorFamily (fun _ : Fin (n+1) => τ)).submatrix (split n).symm (split n).symm)=_
  rw [CacheBatchSplit.tensor,partialLeft_kron,τ.normalized,one_smul,CacheClockAdvance.step_zero]
  ext i j
  simp only [W2.tensorFamily,cacheSector,W2.tensorFamilyDensity,Fin.val_last]
  apply Finset.prod_congr rfl
  intro l _
  rw [if_pos l.isLt]

theorem difference (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    (cache F).matrix-(CacheControllerReturn.cache τ q n).matrix=((n+1 : ℝ)⁻¹) •
      (level (CacheClockAdvance.step n 0) ⊗ₖ tail (n:=n) F.output-
        level (CacheClockAdvance.step n 0) ⊗ₖ tail (n:=n) (tensorPower τ.matrix (n+1))) := by
  have h := congrArg (marginal (frame F)) (CacheRareBranch.difference F)
  simpa only [CacheBatteryBudget.marginal_sub,CacheWorkState.marginal_smul,
    ideal,boundary F hβ hq,ideal_boundary,tail_target (τ:=τ) (q:=q) (n:=n),cache,CacheControllerReturn.cache] using h

theorem accuracy (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    traceDistance (cache F).matrix (cacheState τ q (n+1)) ≤
      traceDistance F.output (tensorPower τ.matrix (n+1))/(n+1 : ℝ) := by
  change traceDistance (cache F).matrix (CacheControllerReturn.cache τ q n).matrix≤_
  rw [TraceMarginal.weighted_distance _ _ _ _ _ (by positivity) (difference F hβ hq),
    TraceMarginal.flag_distance]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left (tail_distance F.output (tensorPower τ.matrix (n+1)))
      (by positivity : 0≤(n+1 : ℝ)⁻¹)

end ScheduleLaw.Blueprint.CacheMarginalAccuracy
