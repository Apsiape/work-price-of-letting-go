import CacheHardwareStock
import CacheServiceHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHardwareHistory
open History CacheHardware
variable {I : Inventory} {S : Schedule I} {n : ℕ} {β : ℝ}

abbrev base (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) : Extension S :=
  CacheServiceGates.extension bare (size_pos bare.b_pos F)
    ((bodyFrame F).trans (activeFrame F)) (source bare.b_pos F)

abbrev prepared (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) : Density (Fin (size F)) :=
  CachePreparationHistory.preparedSource (base bare q F) (preparation F) (preparation_unitary F)

theorem prepared_eq (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    (prepared bare q F).matrix =
      (CacheMixture.output F ⊗ₖ q.matrix).submatrix (bodyFrame F) (bodyFrame F) := by
  have hin : (source bare.b_pos F).matrix =
      (CacheMixture.input F ⊗ₖ q.matrix).submatrix (bodyFrame F) (bodyFrame F) := by
    ext i j
    have h := congrFun (congrFun (CacheHardwareStock.initialized bare.b_pos F hβ hq)
      (bodyFrame F i)) (bodyFrame F j)
    simpa only [submatrix_apply,Equiv.symm_apply_apply] using h
  change evolve (preparation F) (source bare.b_pos F).matrix = _
  rw [preparation,hin,evolve_submatrix_equiv (bodyFrame F),IdleExtension.evolve_idle]
  rfl

variable {d : ℕ} {τ q : Density (Fin d)}

def idealRaw (F : Formation β τ q (n+1)) : Density (CacheFlaggedCircuit.Physical F) :=
  ⟨((CacheControllerReturn.controller F).matrix ⊗ₖ (CacheControllerReturn.rest F).matrix).submatrix
      (CacheControllerReturn.wholeFrame F) (CacheControllerReturn.wholeFrame F),
    ((CacheControllerReturn.controller F).positive.kronecker
      (CacheControllerReturn.rest F).positive).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,
        (CacheControllerReturn.controller F).normalized,(CacheControllerReturn.rest F).normalized,one_mul]⟩

theorem idealRaw_eq (F : Formation β τ q (n+1)) :
    (idealRaw F).matrix=CacheRareBranch.ideal F := by
  ext i j
  have h := congrFun (congrFun (CacheControllerReturn.ideal_product F)
    (CacheControllerReturn.wholeFrame F i)) (CacheControllerReturn.wholeFrame F j)
  simpa only [idealRaw,submatrix_apply,Equiv.symm_apply_apply] using h.symm

def pack (F : Formation β τ q (n+1)) (ρ : Density (CacheFlaggedCircuit.Physical F)) :
    Density (Fin (size F)) :=
  ⟨(ρ.matrix ⊗ₖ q.matrix).submatrix (bodyFrame F) (bodyFrame F),
    (ρ.positive.kronecker q.positive).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,ρ.normalized,q.normalized,one_mul]⟩

def idealSource (F : Formation β τ q (n+1)) : Density (Fin (size F)) := pack F (idealRaw F)

def actualBoundary (F : Formation β τ q (n+1)) : Density (Fin (size F)) :=
  pack F ⟨_,(CacheRareBranch.actual_sector_density F 0).1,(CacheRareBranch.actual_sector_density F 0).2⟩

def idealBoundary (F : Formation β τ q (n+1)) : Density (Fin (size F)) :=
  pack F ⟨_,(CacheRareBranch.ideal_sector_density F 0).1,(CacheRareBranch.ideal_sector_density F 0).2⟩

def idleFrame (F : Formation β τ q (n+1)) : ActiveRest F ≃
    (Fin (n+1) × (Fin n → Fin d)) × ((Fin 2 × Fin 2) × CacheFactoryBody.Rest F) where
  toFun | ((k,u,v),cache,helper) => ((k,cache),(u,v),helper)
  invFun | ((k,cache),(u,v),helper) => ((k,u,v),cache,helper)
  left_inv _ := rfl
  right_inv _ := rfl

def activeStock (F : Formation β τ q (n+1)) : Density (ActiveRest F) :=
  ⟨((CacheControllerReturn.cache τ q n).matrix ⊗ₖ
      (CacheFlaggedCircuit.level ((1 : Fin 2),(0 : Fin 2)) ⊗ₖ CacheFactoryBody.helper F)).submatrix
      (idleFrame F) (idleFrame F),
    ((CacheControllerReturn.cache τ q n).positive.kronecker
      ((pureMatrix_positive _).kronecker (CacheMixture.helper_density F).1)).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,trace_kronecker,
        (CacheControllerReturn.cache τ q n).normalized,(CacheMixture.helper_density F).2]
      simp only [CacheFlaggedCircuit.level,pureMatrix_trace]
      simp⟩

def idleStock (F : Formation β τ q (n+1)) : Density (ActiveRest F × Fin d) :=
  CacheRareProduct.tensorDensity (activeStock F) q

variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1))

theorem ideal_product : (idealSource F).matrix =
    (bare.source.matrix ⊗ₖ (idleStock F).matrix).submatrix
      ((bodyFrame F).trans (activeFrame F)) ((bodyFrame F).trans (activeFrame F)) := by
  change ((idealRaw F).matrix ⊗ₖ ref.matrix).submatrix (bodyFrame F) (bodyFrame F) = _
  rw [idealRaw_eq]
  ext i j
  obtain ⟨⟨⟨⟨k,u,v⟩,batch,c,w,a⟩,reset⟩,rfl⟩ := (bodyFrame F).symm.surjective i
  obtain ⟨⟨⟨⟨k',u',v'⟩,batch',c',w',a'⟩,reset'⟩,rfl⟩ := (bodyFrame F).symm.surjective j
  have h := congrFun (congrFun (CacheRareBranch.ideal_product F)
    (CacheBatchSplit.frame F ((k,u,v),batch,c,w,a)))
    (CacheBatchSplit.frame F ((k',u',v'),batch',c',w',a'))
  simp only [submatrix_apply,Equiv.symm_apply_apply] at h
  simp only [submatrix_apply,Equiv.apply_symm_apply,kroneckerMap_apply]
  rw [h]
  simp only [idleStock,CacheRareProduct.tensorDensity,activeStock,idleFrame,activeFrame,
    Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.coe_fn_mk,submatrix_apply,
    CacheBatchSplit.frame,CacheRareBranch.stock,CacheControllerReturn.cache,kroneckerMap_apply]
  ring

theorem difference (hβ : β≠0) (hq : ref.matrix.PosDef) :
    (prepared bare ref F).matrix-(idealSource F).matrix =
      ((n+1 : ℝ)⁻¹) • ((actualBoundary F).matrix-(idealBoundary F).matrix) := by
  rw [prepared_eq bare ref F hβ hq]
  change (CacheMixture.output F ⊗ₖ ref.matrix).submatrix (bodyFrame F) (bodyFrame F) -
    ((idealRaw F).matrix ⊗ₖ ref.matrix).submatrix (bodyFrame F) (bodyFrame F) = _
  rw [idealRaw_eq]
  ext i j
  have h := congrFun (congrFun (CacheRareBranch.difference F)
    (bodyFrame F i).1) (bodyFrame F j).1
  simp only [Matrix.sub_apply,Matrix.smul_apply] at h
  simp only [actualBoundary,idealBoundary,pack,submatrix_apply,Matrix.sub_apply,
    Matrix.smul_apply,kroneckerMap_apply,Complex.real_smul] at *
  rw [← sub_mul,h]
  ring

/-- Uniform coherent service for the literal one-source hardware, including
its one preparation and its terminal fresh-stock reset. -/
theorem service (hβ : β≠0) (hq : ref.matrix.PosDef) :
    Approximates (CacheHardware.extension bare ref F) bare ((n+1 : ℝ)⁻¹) := by
  intro z t
  change traceDistance (observerOutput (CacheHardware.extension bare ref F) t)
    (observerOutput bare t) ≤ _
  rw [CacheHardware.extension,finalBodyContact_observerOutput,
    CachePreparationHistory.observer_output]
  have h := CacheSourceHistory.approximates (base bare ref F) (prepared bare ref F)
    (idealSource F) (actualBoundary F) (idealBoundary F) ((n+1 : ℝ)⁻¹) (by positivity)
    (difference bare ref F hβ hq) z t
  have hi : observerOutput (CacheSourceHistory.withSource (base bare ref F) (idealSource F)) t =
      observerOutput bare t :=
    CacheServiceHistory.observer_run bare (size_pos bare.b_pos F)
      ((bodyFrame F).trans (activeFrame F)) (idealSource F) (idleStock F)
      (ideal_product bare ref F) t (2*S.visits+1)
  rw [hi] at h
  exact h

end ScheduleLaw.Blueprint.CacheHardwareHistory
