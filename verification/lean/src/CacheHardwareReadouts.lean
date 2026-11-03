import CacheHardwareRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHardwareReadouts
open History CacheHardware CacheHardwareRetained FactoryRegisterOutput
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def activeView (F : Formation β τ q (n+1)) : Fin (size F) ≃ ActiveRest F × (Fin d × Fin d) where
  toFun z := let r := ((bodyFrame F).trans (activeFrame F)) z
             (r.2.1,r.1,r.2.2)
  invFun z := ((bodyFrame F).trans (activeFrame F)).symm (z.2.1,z.1,z.2.2)
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨r,s,t⟩; simp only [Equiv.apply_symm_apply]

def activePack (F : Formation β τ q (n+1)) : ActiveRest F ≃ Fin (c F) × (Fin (w F) × Fin F.aux) where
  toFun
    | ((k,u,v),cache,c0,w0,a0) =>
      (Fintype.equivFin (C F) ((k,cache),c0),Fintype.equivFin (W F) (u,v,w0),a0)
  invFun z :=
    let c0 := (Fintype.equivFin (C F)).symm z.1
    let w0 := (Fintype.equivFin (W F)).symm z.2.1
    ((c0.1.1,w0.1,w0.2.1),c0.1.2,c0.2,w0.2.2,z.2.2)
  left_inv z := by rcases z with ⟨⟨k,u,v⟩,cache,c0,w0,a0⟩; simp only [Equiv.symm_apply_apply]
  right_inv z := by simp only [Prod.mk.eta,Equiv.apply_symm_apply]

def controllerRest (F : Formation β τ q (n+1)) :
    ((Fin (w F) × Fin F.aux) × (Fin d × Fin d)) ≃ Fin (w F) × Fin (r F) where
  toFun | ((w0,a0),s,t) => (w0,Fintype.equivFin (R F) (s,a0,t))
  invFun z := let r0 := (Fintype.equivFin (R F)).symm z.2
              ((z.1,r0.2.1),r0.1,r0.2.2)
  left_inv z := by rcases z with ⟨⟨w0,a0⟩,s,t⟩; simp only [Equiv.symm_apply_apply]
  right_inv z := by simp only [Prod.mk.eta,Equiv.apply_symm_apply]

def batteryRest (F : Formation β τ q (n+1)) :
    ((Fin F.aux × Fin (c F)) × (Fin d × Fin d)) ≃ Fin (r F) × Fin (c F) where
  toFun | ((a0,c0),s,t) => (Fintype.equivFin (R F) (s,a0,t),c0)
  invFun z := let r0 := (Fintype.equivFin (R F)).symm z.1
              ((r0.2.1,z.2),r0.1,r0.2.2)
  left_inv z := by rcases z with ⟨⟨a0,c0⟩,s,t⟩; simp only [Equiv.symm_apply_apply]
  right_inv z := by simp only [Prod.mk.eta,Equiv.apply_symm_apply]

theorem activeView_eq (F : Formation β τ q (n+1)) (M : Mat (Fin (size F))) :
    marginal (activeView F) M=activeReadout F M := by
  ext i j
  simp only [marginal,activeReadout,partialRight,partialLeft,submatrix_apply,activeView,
    Equiv.coe_fn_symm_mk,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem controller_frame (F : Formation β τ q (n+1)) (z : Fin (size F)) :
    FactoryDriven.split (c F) (w F) (r F) z =
      ((FactoryPumpMarginals.compose (activeView F) (activePack F) z).1,
        controllerRest F (FactoryPumpMarginals.compose (activeView F) (activePack F) z).2) := by
  obtain ⟨⟨⟨flags,batch,helper⟩,fresh⟩,rfl⟩ := (bodyFrame F).symm.surjective z
  rw [CacheHardwareStock.split_body]
  simp only [FactoryPumpMarginals.compose,activeView,activePack,controllerRest,
    Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
    Equiv.prodAssoc_apply,Equiv.coe_fn_mk,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  rfl

theorem controller_matrix (F : Formation β τ q (n+1)) (M : Mat (Fin (size F))) :
    partialRight (M.submatrix (FactoryDriven.split (c F) (w F) (r F)).symm
      (FactoryDriven.split (c F) (w F) (r F)).symm) =
        partialRight ((activeReadout F M).submatrix (activePack F).symm (activePack F).symm) := by
  let E := FactoryPumpMarginals.compose (activeView F) (activePack F)
  change marginal (FactoryDriven.split (c F) (w F) (r F)) M =
    marginal (activePack F) (activeReadout F M)
  rw [reframe E (FactoryDriven.split (c F) (w F) (r F)) (controllerRest F)
    (controller_frame F) M,FactoryPumpMarginals.marginal_compose,activeView_eq]

theorem battery_matrix (F : Formation β τ q (n+1)) (M : Mat (Fin (size F))) :
    partialRight (partialLeft (M.submatrix (FactoryDriven.split (c F) (w F) (r F)).symm
      (FactoryDriven.split (c F) (w F) (r F)).symm)) =
        partialRight (partialLeft ((activeReadout F M).submatrix (activePack F).symm (activePack F).symm)) := by
  let E := FactoryPumpMarginals.compose (activeView F) ((activePack F).trans FactoryWorkPacking.workView)
  let Q := (FactoryDriven.split (c F) (w F) (r F)).trans FactoryWorkPacking.workView
  have hf : ∀ z,Q z=((E z).1,batteryRest F (E z).2) := by
    intro z
    obtain ⟨⟨⟨flags,batch,helper⟩,fresh⟩,rfl⟩ := (bodyFrame F).symm.surjective z
    simp only [Q,Equiv.trans_apply,CacheHardwareStock.split_body]
    simp only [E,FactoryPumpMarginals.compose,activeView,activePack,batteryRest,
      FactoryWorkPacking.workView,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,
      Equiv.refl_apply,Equiv.prodAssoc_apply,Equiv.coe_fn_mk,
      Equiv.apply_symm_apply,Equiv.symm_apply_apply]
    rfl
  rw [FactoryWorkPacking.work_marginal,FactoryWorkPacking.work_marginal]
  change marginal Q M=marginal ((activePack F).trans FactoryWorkPacking.workView) (activeReadout F M)
  rw [reframe E Q (batteryRest F) hf M,FactoryPumpMarginals.marginal_compose,activeView_eq]

variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem controller_output (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    Driven.controllerFinal (hardware bare ref F service) t =
      partialRight ((partialLeft ((CacheMixture.output F).submatrix
        (sourceFrame F).symm (sourceFrame F).symm)).submatrix (activePack F).symm (activePack F).symm) := by
  change partialRight ((bodyOutput (CacheHardware.extension bare ref F) t).submatrix
    (FactoryDriven.split (c F) (w F) (r F)).symm
    (FactoryDriven.split (c F) (w F) (r F)).symm) = _
  rw [controller_matrix,active_output_eq bare ref F hβ hq t]

theorem battery_output (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    Driven.batteryFinal (hardware bare ref F service) t =
      partialRight (partialLeft ((partialLeft ((CacheMixture.output F).submatrix
        (sourceFrame F).symm (sourceFrame F).symm)).submatrix (activePack F).symm (activePack F).symm)) := by
  change partialRight (partialLeft ((bodyOutput (CacheHardware.extension bare ref F) t).submatrix
    (FactoryDriven.split (c F) (w F) (r F)).symm
    (FactoryDriven.split (c F) (w F) (r F)).symm)) = _
  rw [battery_matrix,active_output_eq bare ref F hβ hq t]

end ScheduleLaw.Blueprint.CacheHardwareReadouts
