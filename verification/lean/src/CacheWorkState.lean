import CacheHardwareReadouts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheWorkState
open History CacheHardware CacheHardwareRetained CacheHardwareReadouts FactoryRegisterOutput
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

abbrev Rest (F : Formation β τ q (n+1)) :=
  Fin (n+1) × ((Fin (n+1) → Fin d) × (Fin F.hardware.c × Fin F.aux))

def frame (F : Formation β τ q (n+1)) : CacheFlaggedCircuit.Physical F ≃ W F × Rest F where
  toFun | ((k,u,v),batch,c0,w0,a0) => ((u,v,w0),k,batch,c0,a0)
  invFun | ((u,v,w0),k,batch,c0,a0) => ((k,u,v),batch,c0,w0,a0)
  left_inv _ := rfl
  right_inv _ := rfl

def battery (F : Formation β τ q (n+1)) (M : Mat (CacheFlaggedCircuit.Physical F)) : Mat (Fin (w F)) :=
  (marginal (frame F) M).submatrix (Fintype.equivFin (W F)).symm (Fintype.equivFin (W F)).symm

def flagged (F : Formation β τ q (n+1)) (u v : Fin 2) (B : Mat (Fin F.hardware.w)) : Mat (W F) :=
  (CacheFlaggedCircuit.level (u,v) ⊗ₖ B).submatrix
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin F.hardware.w)).symm
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin F.hardware.w)).symm

def batchWork (F : Formation β τ q (n+1)) (M : Mat ((Fin (n+1) → Fin d) × CacheFactoryBody.Rest F)) :
    Mat (Fin F.hardware.w) := partialRight (partialLeft (partialLeft M))

def remaining (F : Formation β τ q (n+1)) :
    (Fin d × (Fin F.aux × Fin (c F))) ≃ Rest F where
  toFun z := let c0 := (Fintype.equivFin (C F)).symm z.2.2
             (c0.1.1,(CacheBatchSplit.split n).symm (z.1,c0.1.2),c0.2,z.2.1)
  invFun
    | (k,batch,c0,a0) =>
      let b := CacheBatchSplit.split n batch
      (b.1,a0,Fintype.equivFin (C F) ((k,b.2),c0))
  left_inv z := by simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Prod.mk.eta]
  right_inv z := by rcases z with ⟨k,batch,c0,a0⟩; simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Prod.mk.eta]

theorem sum_reverse {a b c : Type} [Fintype a] [Fintype b] [Fintype c] (f : a → b → c → ℂ) :
    (∑ i,∑ j,∑ k,f i j k) = ∑ k,∑ j,∑ i,f i j k := by
  calc _ = ∑ i,∑ k,∑ j,f i j k := by
         apply Finset.sum_congr rfl
         intro i _
         exact Finset.sum_comm
       _ = ∑ k,∑ i,∑ j,f i j k := Finset.sum_comm
       _ = _ := by
         apply Finset.sum_congr rfl
         intro k _
         exact Finset.sum_comm

theorem marginal_smul {a b c : Type} [Fintype c] (e : a ≃ b × c) (M : Mat a) (x : ℝ) :
    marginal e (x • M)=x • marginal e M := by
  ext i j
  simp only [marginal,partialRight,submatrix_apply,Matrix.smul_apply,Finset.smul_sum]

theorem marginal_sum {a b c k : Type} [Fintype c] [Fintype k] (e : a ≃ b × c) (M : k → Mat a) :
    marginal e (∑ j,M j)=∑ j,marginal e (M j) := by
  ext i j
  simp only [marginal,partialRight,submatrix_apply,Matrix.sum_apply]
  exact Finset.sum_comm

def idealBatch (F : Formation β τ q (n+1)) (j : Fin (n+1)) : Density (Fin (n+1) → Fin d) :=
  ⟨(τ.matrix ⊗ₖ (CacheBatchSplit.cacheSector τ q n (CacheClockAdvance.step n j)).matrix).submatrix
      (CacheBatchSplit.split n) (CacheBatchSplit.split n),
    (τ.positive.kronecker (CacheBatchSplit.cacheSector τ q n _).positive).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,τ.normalized,
        (CacheBatchSplit.cacheSector τ q n _).normalized,one_mul]⟩

theorem ideal_sector_eq (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    CacheRareBranch.idealSector F j =
      CacheFlaggedCircuit.level (CacheClockAdvance.step n j,1,0) ⊗ₖ
        ((idealBatch F j).matrix ⊗ₖ CacheFactoryBody.helper F) := by
  rw [CacheBatchSplit.level_prod]
  ext ⟨⟨k,u,v⟩,batch,h⟩ ⟨⟨k',u',v'⟩,batch',h'⟩
  simp only [CacheRareBranch.idealSector,CacheRareBranch.stock,CacheBatchSplit.frame,idealBatch,
    submatrix_apply,Equiv.coe_fn_mk,kroneckerMap_apply]
  ring

theorem helper_work (F : Formation β τ q (n+1))
    (B : Density (Fin (n+1) → Fin d)) :
    batchWork F (B.matrix ⊗ₖ CacheFactoryBody.helper F) =
      pureMatrix (fun j => if j=F.hardware.initialLevel then 1 else 0) := by
  letI : Nonempty (Fin F.aux) := ⟨⟨0,F.aux_pos⟩⟩
  simp only [batchWork,partialLeft_kron,B.normalized,one_smul,CacheFactoryBody.helper,
    F.hardware.controller.normalized,partialRight_kron,gibbs_trace]

theorem packed (F : Formation β τ q (n+1)) (M : Mat (CacheFlaggedCircuit.Physical F)) :
    partialRight (partialLeft ((partialLeft (M.submatrix
      (sourceFrame F).symm (sourceFrame F).symm)).submatrix (activePack F).symm (activePack F).symm)) =
        battery F M := by
  let E := FactoryMarginals.outsideFrame (sourceFrame F) ((activePack F).trans FactoryWorkPacking.workView)
  let Q := (frame F).trans (Equiv.prodCongr (Fintype.equivFin (W F)) (Equiv.refl (Rest F)))
  have hf : ∀ z,Q z=((E z).1,remaining F (E z).2) := by
    intro z
    rcases z with ⟨⟨k,u,v⟩,batch,c0,w0,a0⟩
    simp only [E,Q,FactoryMarginals.outsideFrame,sourceFrame,activePack,frame,remaining,
      FactoryWorkPacking.workView,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,
      Equiv.refl_apply,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
    simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  rw [FactoryWorkPacking.work_marginal]
  change marginal ((activePack F).trans FactoryWorkPacking.workView)
    (partialLeft (M.submatrix (sourceFrame F).symm (sourceFrame F).symm)) = marginal Q M
  have ho : marginal E M = marginal ((activePack F).trans FactoryWorkPacking.workView)
      (partialLeft (M.submatrix (sourceFrame F).symm (sourceFrame F).symm)) :=
    FactoryMarginals.outside_marginal (sourceFrame F) ((activePack F).trans FactoryWorkPacking.workView) M
  exact ho.symm.trans (reframe E Q (remaining F) hf M).symm

theorem sector (F : Formation β τ q (n+1)) (k : Fin (n+1)) (u v : Fin 2)
    (M : Mat ((Fin (n+1) → Fin d) × CacheFactoryBody.Rest F)) :
    marginal (frame F) (CacheFlaggedCircuit.level (k,u,v) ⊗ₖ M) = flagged F u v (batchWork F M) := by
  rw [CacheBatchSplit.level_prod k (u,v)]
  ext ⟨u0,v0,w0⟩ ⟨u1,v1,w1⟩
  simp only [marginal,frame,partialRight,partialLeft,batchWork,flagged,submatrix_apply,
    Equiv.coe_fn_symm_mk,Equiv.prodAssoc_symm_apply,kroneckerMap_apply,Fintype.sum_prod_type,
    CacheFlaggedCircuit.level,pureMatrix,Prod.mk.injEq]
  split_ifs <;> simp_all [Finset.mul_sum,Finset.sum_mul]
  exact sum_reverse _

theorem factory_work (F : Formation β τ q (n+1)) :
    batchWork F (CacheFactoryBody.result F)=Driven.batteryFinal F.hardware (idleTester F.schedule) := by
  ext i j
  simp only [batchWork,CacheFactoryBody.result,Driven.batteryFinal,Driven.batteryReservoirFinal,
    partialRight,partialLeft,submatrix_apply,CacheFactoryBody.coordinates,Equiv.coe_fn_symm_mk,
    Fintype.sum_prod_type]
  conv_rhs =>
    rw [← Equiv.sum_comp F.reservoirSplit.symm]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact sum_reverse _

theorem rotated_work (F : Formation β τ q (n+1)) :
    batchWork F (evolve
      ((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ ⊗ₖ
        (1 : Mat (CacheFactoryBody.Rest F))) (CacheFactoryBody.result F)) =
      Driven.batteryFinal F.hardware (idleTester F.schedule) := by
  unfold batchWork
  rw [partialLeft_evolve_kron_one _ _ (Recorder.permutation_unitary _)]
  exact factory_work F

theorem ideal_sector_work (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    marginal (frame F) (CacheRareBranch.idealSector F j) =
      CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) := by
  rw [ideal_sector_eq,sector,helper_work]
  rw [flagged]
  ext ⟨u,v,w⟩ ⟨u',v',w'⟩
  simp only [CacheFlaggedCircuit.level,pureMatrix,CacheWorkLedger.nominal,submatrix_apply,
    Equiv.prodAssoc_symm_apply,Prod.mk.injEq,kroneckerMap_apply]
  split_ifs <;> simp_all

theorem boundary_work (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    marginal (frame F) (evolve (CacheFlaggedCircuit.circuit F) (CacheFlaggedCircuit.inputSector F 0)) =
      flagged F 1 1 (Driven.batteryFinal F.hardware (idleTester F.schedule)) := by
  rw [CacheFlaggedCircuit.boundary F hβ hq]
  simpa only [CacheClockAdvance.target,if_true] using
    (sector F (CacheClockAdvance.step n 0) 1 1 _).trans
      (congrArg (flagged F 1 1) (rotated_work F))

theorem ideal_work (F : Formation β τ q (n+1)) :
    marginal (frame F) (CacheRareBranch.ideal F)=CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) := by
  rw [CacheRareBranch.ideal,marginal_smul,marginal_sum]
  simp_rw [ideal_sector_work]
  ext i j
  simp only [Matrix.smul_apply,Matrix.sum_apply]
  simp only [Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Complex.real_smul]
  push_cast
  field_simp


variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem output (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    Driven.batteryFinal (hardware bare ref F service) t=battery F (CacheMixture.output F) := by
  rw [CacheHardwareReadouts.battery_output bare ref F service hβ hq t,packed]

end ScheduleLaw.Blueprint.CacheWorkState
