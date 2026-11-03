import CacheHardware

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHardwareStock
open History CacheHardware

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

theorem reservoir (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    (gibbs β (HR F)).submatrix (Fintype.equivFin (R F)) (Fintype.equivFin (R F)) =
      q.matrix ⊗ₖ (gibbs β F.auxiliaryHamiltonian ⊗ₖ q.matrix) := by
  rw [HR,FactoryGibbs.gibbs_reindex]
  have hs : ((gibbs β (rawHR F)).submatrix (Fintype.equivFin (R F)).symm
      (Fintype.equivFin (R F)).symm).submatrix (Fintype.equivFin (R F))
        (Fintype.equivFin (R F))=gibbs β (rawHR F) := by
    ext i j; simp only [submatrix_apply,Equiv.symm_apply_apply]
  rw [hs,rawHR,FactoryGibbs.gibbs_product,FactoryGibbs.gibbs_product,
    FactoryGibbs.tangent_gibbs β hβ q hq]

theorem split_body (F : Formation β τ q (n+1)) (z : Physical F) :
    FactoryDriven.split (c F) (w F) (r F) ((bodyFrame F).symm z) =
      (Fintype.equivFin (C F) ((physicalFrame F z).1),
       Fintype.equivFin (W F) ((physicalFrame F z).2.1),
       Fintype.equivFin (R F) ((physicalFrame F z).2.2)) := by
  simp only [bodyFrame,Equiv.symm_trans_apply,Equiv.apply_symm_apply,
    Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.symm_symm,Prod.map_apply]
  rfl

/-- The literal original Driven source is exactly the invested correlated
cache, all factory helpers, one fresh q source and the independent terminal
q reset stock, under the actual physical register coordinates. -/
theorem initialized (hd : 0<d) (F : Formation β τ q (n+1))
    (hβ : β≠0) (hq : q.matrix.PosDef) :
    (source hd F).matrix.submatrix (bodyFrame F).symm (bodyFrame F).symm =
      CacheMixture.input F ⊗ₖ q.matrix := by
  have hs (i j : Fin (size F)) : (source hd F).matrix i j=
      (controller F).matrix ((FactoryDriven.split (c F) (w F) (r F) i).1)
        ((FactoryDriven.split (c F) (w F) (r F) j).1) *
      (pureMatrix (fun k => if k=initial F then 1 else 0)
        ((FactoryDriven.split (c F) (w F) (r F) i).2.1)
        ((FactoryDriven.split (c F) (w F) (r F) j).2.1) *
        gibbs β (HR F) ((FactoryDriven.split (c F) (w F) (r F) i).2.2)
          ((FactoryDriven.split (c F) (w F) (r F) j).2.2)) := rfl
  ext z z'
  obtain ⟨⟨⟨cache,c0⟩,⟨main,aux,w0⟩,b,a,reset⟩,rfl⟩ := (physicalFrame F).symm.surjective z
  obtain ⟨⟨⟨cache',c0'⟩,⟨main',aux',w0'⟩,b',a',reset'⟩,rfl⟩ := (physicalFrame F).symm.surjective z'
  have hr := congrArg (fun M => M (b,a,reset) (b',a',reset')) (reservoir F hβ hq)
  simp only [submatrix_apply,kroneckerMap_apply] at hr
  have hi := congrArg (fun M => M (cache,(main,aux),b,c0,w0,a)
    (cache',(main',aux'),b',c0',w0',a')) (CacheMixture.input_product F)
  simp only [submatrix_apply,kroneckerMap_apply,CacheFactoryBody.helper,
    CacheBatchSplit.frame,Equiv.coe_fn_symm_mk] at hi
  simp only [submatrix_apply,hs,split_body,Equiv.apply_symm_apply,controller,
    Equiv.symm_apply_apply,kroneckerMap_apply]
  rw [hr]
  simp only [physicalFrame,Equiv.coe_fn_symm_mk,kroneckerMap_apply]
  rw [hi]
  have hw (u : W F) : Fintype.equivFin (W F) u=initial F ↔ u=CacheWorkLedger.initial F := by
    change Fintype.equivFin (W F) u=Fintype.equivFin (W F) (CacheWorkLedger.initial F) ↔ _
    exact (Fintype.equivFin (W F)).injective.eq_iff
  by_cases h1 : main=0 <;> by_cases h2 : main'=0 <;>
    by_cases h3 : aux=0 <;> by_cases h4 : aux'=0 <;>
    by_cases h5 : w0=F.hardware.initialLevel <;> by_cases h6 : w0'=F.hardware.initialLevel <;>
    simp [pureMatrix,hw,CacheWorkLedger.initial,CacheFlaggedCircuit.level,Prod.mk.injEq,
      CacheControllerReturn.controller,CacheControllerReturn.cache,CacheRareProduct.tensorDensity,
      kroneckerMap_apply,h1,h2,h3,h4,h5,h6] <;> ring

end ScheduleLaw.Blueprint.CacheHardwareStock
