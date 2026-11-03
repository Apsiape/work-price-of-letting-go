import CacheMarginalFactor
import CacheRefundBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.CacheControllerRefund
open History CacheHardware CacheHardwareRetained CacheHardwareReadouts FactoryRegisterOutput
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def restPack (F : Formation β τ q (n+1)) :
    (Fin d × (Fin (w F) × Fin F.aux)) ≃ CacheControllerReturn.Rest F where
  toFun z := let w0 := (Fintype.equivFin (W F)).symm z.2.1
             ((w0.1,w0.2.1),z.1,w0.2.2,z.2.2)
  invFun | ((u,v),s,w0,a0) => (s,Fintype.equivFin (W F) (u,v,w0),a0)
  left_inv z := by simp only [Equiv.apply_symm_apply,Prod.mk.eta]
  right_inv z := by rcases z with ⟨⟨u,v⟩,s,w0,a0⟩; simp only [Equiv.symm_apply_apply]

variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem raw_output (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    (Driven.controllerFinal (hardware bare ref F service) t).submatrix
      (Fintype.equivFin (C F)) (Fintype.equivFin (C F)) =
        marginal (CacheControllerReturn.wholeFrame F) (CacheMixture.output F) := by
  let E := FactoryMarginals.outsideFrame (sourceFrame F) (activePack F)
  let Q := E.trans (Equiv.prodCongr (Fintype.equivFin (C F)).symm (Equiv.refl _))
  have hf : ∀ z,CacheControllerReturn.wholeFrame F z=((Q z).1,restPack F (Q z).2) := by
    rintro ⟨⟨k,u,v⟩,batch,c0,w0,a0⟩
    simp only [Q,E,FactoryMarginals.outsideFrame,sourceFrame,activePack,restPack,
      CacheControllerReturn.wholeFrame,CacheBatchSplit.frame,Equiv.trans_apply,
      Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.coe_fn_mk,
      Equiv.symm_apply_apply]
  have he (M : Mat (CacheFlaggedCircuit.Physical F)) :
      marginal Q M=(marginal E M).submatrix (Fintype.equivFin (C F)) (Fintype.equivFin (C F)) := by
    ext i j
    simp only [marginal,Q,Equiv.symm_trans_apply,Equiv.prodCongr_symm,
      Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_symm,Equiv.refl_apply,
      Equiv.symm_symm,partialRight,submatrix_apply]
  rw [CacheHardwareReadouts.controller_output bare ref F service hβ hq t]
  change (marginal (activePack F) (partialLeft ((CacheMixture.output F).submatrix
    (sourceFrame F).symm (sourceFrame F).symm))).submatrix _ _ = _
  have ho : marginal E (CacheMixture.output F)=marginal (activePack F)
      (partialLeft ((CacheMixture.output F).submatrix (sourceFrame F).symm (sourceFrame F).symm)) :=
    FactoryMarginals.outside_marginal (sourceFrame F) (activePack F) (CacheMixture.output F)
  rw [← ho,← he (CacheMixture.output F)]
  exact (reframe Q (CacheControllerReturn.wholeFrame F) (restPack F) hf (CacheMixture.output F)).symm

theorem actual_factor (hβ : β≠0) (hq : ref.matrix.PosDef)
    (hexact : ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)),
      FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=F.hardware.controller.matrix ⊗ₖ σ.matrix)
    {z : ℕ} (t : Tester S z) :
    (Driven.controllerFinal (hardware bare ref F service) t).submatrix
      (Fintype.equivFin (C F)) (Fintype.equivFin (C F)) =
        (CacheMarginalAccuracy.cache F).matrix ⊗ₖ F.hardware.controller.matrix := by
  obtain ⟨σ,hσ⟩ := hexact
  obtain ⟨ω,hω⟩ := FactoryCacheMarginal.result_product F σ hσ
  rw [raw_output bare ref F service hβ hq t]
  exact CacheMarginalFactor.factor F hβ hq ω hω

theorem entropy_change (hβ : β≠0) (hq : ref.matrix.PosDef)
    (hexact : ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)),
      FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=F.hardware.controller.matrix ⊗ₖ σ.matrix)
    {z : ℕ} (t : Tester S z) :
    Driven.controllerEntropyChange (hardware bare ref F service) t=
      entropy (CacheMarginalAccuracy.cache F).matrix-entropy (CacheControllerReturn.cache bare.source ref n).matrix := by
  have hp := partialRight_positive ((bodyOutput_density (hardware bare ref F service).extension t).1.submatrix
    (hardware bare ref F service).split.symm)
  have he := entropy_submatrix_equiv (Fintype.equivFin (C F))
    (Driven.controllerFinal (hardware bare ref F service) t) hp.isHermitian
  rw [actual_factor bare ref F service hβ hq hexact t] at he
  have hs := entropy_submatrix_equiv (Fintype.equivFin (C F)).symm
    (CacheControllerReturn.controller F).matrix (CacheControllerReturn.controller F).positive.isHermitian
  change entropy (Driven.controllerFinal (hardware bare ref F service) t)-entropy (controller F).matrix=_
  rw [← he,show entropy (controller F).matrix=entropy (CacheControllerReturn.controller F).matrix from hs]
  change entropy ((CacheMarginalAccuracy.cache F).matrix ⊗ₖ F.hardware.controller.matrix)-
    entropy ((CacheControllerReturn.cache bare.source ref n).matrix ⊗ₖ F.hardware.controller.matrix)=_
  rw [entropy_density_product,entropy_density_product]
  ring

theorem entropy_refund (hβ : β≠0) (hq : ref.matrix.PosDef)
    (hexact : ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)),
      FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=F.hardware.controller.matrix ⊗ₖ σ.matrix)
    {z : ℕ} (t : Tester S z) (ε : ℝ) (hε : 0≤ε)
    (hacc : traceDistance F.output (tensorPower bare.source.matrix (n+1))≤ε) :
    |Driven.controllerEntropyChange (hardware bare ref F service) t|≤CacheRefundBounds.modulus bare.b ε := by
  rw [entropy_change bare ref F service hβ hq hexact t]
  apply CacheRefundBounds.entropy_refund bare.b_pos _ _ ε hε
  exact (CacheMarginalAccuracy.accuracy F hβ hq).trans
    (div_le_div_of_nonneg_right hacc (by positivity))

end ScheduleLaw.Blueprint.CacheControllerRefund
