import CacheControllerHistory
import CacheBatteryBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHardwareReturn
open History CacheHardware CacheHardwareHistory
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}
abbrev Rest (F : Formation β τ q (n+1)) := W F × (Fin F.aux × Fin d)
abbrev serviceFrame (F : Formation β τ q (n+1)) := (bodyFrame F).trans (activeFrame F)

def retainedFrame (F : Formation β τ q (n+1)) : (ActiveRest F × Fin d) ≃ C F × Rest F where
  toFun | (((k,u,v),cache,c0,w0,a0),fresh) => (((k,cache),c0),(u,v,w0),a0,fresh)
  invFun | (((k,cache),c0),(u,v,w0),a0,fresh) => (((k,u,v),cache,c0,w0,a0),fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def stockFrame (F : Formation β τ q (n+1)) : (Fin d × Rest F) ≃ CacheControllerReturn.Rest F × Fin d where
  toFun | (s,(u,v,w0),a0,fresh) => (((u,v),s,w0,a0),fresh)
  invFun | (((u,v),s,w0,a0),fresh) => (s,(u,v,w0),a0,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def stock (F : Formation β τ q (n+1)) : Density (Fin d × Rest F) :=
  ⟨((CacheControllerReturn.rest F).matrix ⊗ₖ q.matrix).submatrix (stockFrame F) (stockFrame F),
    ((CacheControllerReturn.rest F).positive.kronecker q.positive).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,(CacheControllerReturn.rest F).normalized,q.normalized,one_mul]⟩

def restReset (F : Formation β τ q (n+1)) : Equiv.Perm (Fin d × Rest F) where
  toFun | (s,w0,a0,fresh) => (fresh,w0,a0,s)
  invFun | (s,w0,a0,fresh) => (fresh,w0,a0,s)
  left_inv _ := rfl
  right_inv _ := rfl

variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1))

abbrev sourceFrame := CacheControllerHistory.sourceWires bare (serviceFrame F) (retainedFrame F)
abbrev globalFrame (z : ℕ) := CacheControllerHistory.globalWires bare (serviceFrame F) (retainedFrame F) z

def wholeFrame (z : ℕ) : Global (base bare ref F) z ≃
    Fin (c F) × ((Fin (w F) × Fin (r F)) × (Payload I × Fin z)) :=
  (Equiv.prodCongr (FactoryDriven.split (c F) (w F) (r F)) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

def restPacking (z : ℕ) : (Global bare z × Rest F) ≃
    ((Fin (w F) × Fin (r F)) × (Payload I × Fin z)) where
  toFun | ((s,o),w0,a0,fresh) => ((Fintype.equivFin (W F) w0,Fintype.equivFin (R F) (s,a0,fresh)),o)
  invFun
    | ((w0,r0),o) =>
      let r1 := (Fintype.equivFin (R F)).symm r0
      ((r1.1,o),(Fintype.equivFin (W F)).symm w0,r1.2.1,r1.2.2)
  left_inv z := by rcases z with ⟨⟨s,o⟩,w0,a0,fresh⟩; simp only [Equiv.symm_apply_apply]
  right_inv z := by simp only [Prod.mk.eta,Equiv.apply_symm_apply]

abbrev served (ρ : Density (Fin (size F))) : Extension S :=
  finalBodyContact (CacheSourceHistory.withSource (base bare ref F) ρ) (reset F) (reset_unitary F)

def whole (ρ : Density (Fin (size F))) {z : ℕ} (t : Tester S z) :
    Mat (Fin (c F) × ((Fin (w F) × Fin (r F)) × (Payload I × Fin z))) :=
  (finalState (served bare ref F ρ) t).submatrix (wholeFrame bare ref F z).symm (wholeFrame bare ref F z).symm

def wholeDensity (ρ : Density (Fin (size F))) {z : ℕ} (t : Tester S z) :
    Density (Fin (c F) × ((Fin (w F) × Fin (r F)) × (Payload I × Fin z))) :=
  ⟨whole bare ref F ρ t,(run_density (served bare ref F ρ) t _).1.submatrix _,by
    rw [whole,submatrix_trace_equiv (wholeFrame bare ref F z).symm]; exact (run_density (served bare ref F ρ) t _).2⟩

theorem source_product : (idealSource F).matrix.submatrix (sourceFrame bare ref F).symm (sourceFrame bare ref F).symm =
    (CacheControllerReturn.controller F).matrix ⊗ₖ (stock F).matrix := by
  ext ⟨⟨⟨k,cache⟩,c0⟩,s,⟨u,v,w0⟩,a0,fresh⟩
    ⟨⟨⟨k',cache'⟩,c0'⟩,s',⟨u',v',w0'⟩,a0',fresh'⟩
  simp only [sourceFrame,CacheControllerHistory.sourceWires,serviceFrame,retainedFrame,
    idealSource,pack,idealRaw,CacheControllerReturn.wholeFrame,CacheBatchSplit.frame,
    activeFrame,stock,stockFrame,submatrix_apply,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,
    Equiv.symm_trans_apply,Equiv.apply_symm_apply,Equiv.symm_apply_apply,kroneckerMap_apply]
  ring

theorem reset_factor : (reset F).submatrix (sourceFrame bare ref F).symm (sourceFrame bare ref F).symm =
    (1 : Mat (C F)) ⊗ₖ (restReset F).permMatrix ℂ := by
  ext ⟨⟨⟨k,cache⟩,c0⟩,s,⟨u,v,w0⟩,a0,fresh⟩
    ⟨⟨⟨k',cache'⟩,c0'⟩,s',⟨u',v',w0'⟩,a0',fresh'⟩
  simp only [reset,sourceFrame,CacheControllerHistory.sourceWires,serviceFrame,retainedFrame,
    submatrix_apply,Equiv.coe_fn_symm_mk,Equiv.symm_trans_apply,Equiv.apply_symm_apply,
    Equiv.symm_apply_apply,activeFrame,Recorder.permutation_entry,FactoryReset.swap,restReset,
    Equiv.coe_fn_mk,kroneckerMap_apply,one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem ideal_product {z : ℕ} (t : Tester S z) :
    ∃ σ : Density (Global bare z × Rest F),
      (finalState (served bare ref F (idealSource F)) t).submatrix (globalFrame bare ref F z).symm
        (globalFrame bare ref F z).symm = (CacheControllerReturn.controller F).matrix ⊗ₖ σ.matrix := by
  exact CacheControllerHistory.contact_product bare (serviceFrame F) (retainedFrame F)
    (size_pos bare.b_pos F) (idealSource F) (CacheControllerReturn.controller F) (stock F)
    (source_product bare ref F) (reset F) (reset_unitary F) ((restReset F).permMatrix ℂ)
    (Recorder.permutation_unitary _) (reset_factor bare ref F) t

theorem packing (z : ℕ)
    (i : Fin (c F) × ((Fin (w F) × Fin (r F)) × (Payload I × Fin z))) :
    globalFrame bare ref F z ((wholeFrame bare ref F z).symm i) =
      ((Fintype.equivFin (C F)).symm i.1,(restPacking bare ref F z).symm i.2) := by
  rcases i with ⟨ci,⟨wi,ri⟩,o⟩
  change globalFrame bare ref F z ((FactoryDriven.split (c F) (w F) (r F)).symm (ci,wi,ri),o) = _
  obtain ⟨⟨⟨k,cache⟩,c0⟩,rfl⟩ := (Fintype.equivFin (C F)).surjective ci
  obtain ⟨⟨u,v,w0⟩,rfl⟩ := (Fintype.equivFin (W F)).surjective wi
  obtain ⟨⟨s,a0,fresh⟩,rfl⟩ := (Fintype.equivFin (R F)).surjective ri
  simp only [wholeFrame,globalFrame,CacheControllerHistory.globalWires,serviceFrame,bodyFrame,
    Equiv.symm_trans_apply,Equiv.trans_apply,Equiv.prodAssoc_symm_apply,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply,Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk,Equiv.apply_symm_apply,Equiv.symm_apply_apply,physicalFrame,activeFrame,
    retainedFrame,restPacking]
  all_goals rfl

theorem ideal_whole {z : ℕ} (t : Tester S z) :
    ∃ σ : Density ((Fin (w F) × Fin (r F)) × (Payload I × Fin z)),
      whole bare ref F (idealSource F) t=(controller F).matrix ⊗ₖ σ.matrix := by
  obtain ⟨σ,hσ⟩ := ideal_product bare ref F t
  let ω : Density ((Fin (w F) × Fin (r F)) × (Payload I × Fin z)) :=
    ⟨σ.matrix.submatrix (restPacking bare ref F z).symm (restPacking bare ref F z).symm,
      σ.positive.submatrix _,by
        rw [submatrix_trace_equiv (restPacking bare ref F z).symm]; exact σ.normalized⟩
  have hi (i : Fin (c F) × ((Fin (w F) × Fin (r F)) × (Payload I × Fin z))) :
      (globalFrame bare ref F z).symm
        ((Fintype.equivFin (C F)).symm i.1,(restPacking bare ref F z).symm i.2) =
          (wholeFrame bare ref F z).symm i := by
    apply (globalFrame bare ref F z).injective
    rw [Equiv.apply_symm_apply,packing]
  refine ⟨ω,?_⟩
  ext i j
  have hh := congrFun (congrFun hσ
    ((Fintype.equivFin (C F)).symm i.1,(restPacking bare ref F z).symm i.2))
    ((Fintype.equivFin (C F)).symm j.1,(restPacking bare ref F z).symm j.2)
  simp only [submatrix_apply,hi] at hh
  simpa only [whole,controller,ω,submatrix_apply,kroneckerMap_apply] using hh

theorem actual_whole (service : ℝ) {z : ℕ} (t : Tester S z) :
    FactoryControllerReturn.wholeState (hardware bare ref F service) t =
      whole bare ref F (prepared bare ref F) t := by
  have hr := CachePreparationHistory.run_source (base bare ref F) (preparation F)
    (preparation_unitary F) t (2*S.visits+1) (by omega)
  have hf : finalState (CacheHardware.extension bare ref F) t =
      finalState (served bare ref F (prepared bare ref F)) t := by
    change finalState (finalBodyContact
      (CacheServiceGates.prepare (base bare ref F) (preparation F) (preparation_unitary F))
      (reset F) (reset_unitary F)) t = _
    rw [finalBodyContact_finalState,finalBodyContact_finalState]
    exact congrArg (evolve (reset F ⊗ₖ (1 : Mat (Payload I × Fin z)))) hr
  change (finalState (CacheHardware.extension bare ref F) t).submatrix
    (wholeFrame bare ref F z).symm (wholeFrame bare ref F z).symm = _
  rw [hf]
  rfl

theorem difference (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    whole bare ref F (prepared bare ref F) t-whole bare ref F (idealSource F) t =
      ((n+1 : ℝ)⁻¹) • (whole bare ref F (actualBoundary F) t-whole bare ref F (idealBoundary F) t) := by
  have hs := CacheSourceHistory.difference (base bare ref F) (prepared bare ref F)
    (idealSource F) (actualBoundary F) (idealBoundary F) ((n+1 : ℝ)⁻¹)
    (CacheHardwareHistory.difference bare ref F hβ hq) t (2*S.visits+1)
  have hh := congrArg (fun M => evolve (reset F ⊗ₖ (1 : Mat (Payload I × Fin z))) M) hs
  let fm (ρ : Density (Fin (size F))) : Mat (Global (base bare ref F) z) :=
    finalState (served bare ref F ρ) t
  have hfm (ρ : Density (Fin (size F))) : fm ρ =
      evolve (reset F ⊗ₖ (1 : Mat (Payload I × Fin z)))
        (ScheduleLaw.run (CacheSourceHistory.withSource (base bare ref F) ρ) t (2*S.visits+1)) :=
    finalBodyContact_finalState _ _ _ t
  have hf : fm (prepared bare ref F)-fm (idealSource F) = ((n+1 : ℝ)⁻¹) •
      (fm (actualBoundary F)-fm (idealBoundary F)) := by
    simp only [hfm]
    simpa only [evolve,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul] using hh
  ext i j
  have he := congrFun (congrFun hf ((wholeFrame bare ref F z).symm i))
    ((wholeFrame bare ref F z).symm j)
  simpa only [fm,whole,submatrix_apply,Matrix.sub_apply,Matrix.smul_apply] using he

theorem whole_rest (service : ℝ) (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    Driven.controllerProductDefect (hardware bare ref F service) t≤2/(n+1 : ℝ) := by
  obtain ⟨σ,hσ⟩ := ideal_whole bare ref F t
  have hh := difference bare ref F hβ hq t
  rw [hσ] at hh
  have h := CacheRareProduct.whole_rest (controller F) σ
    (whole bare ref F (prepared bare ref F) t)
    (wholeDensity bare ref F (actualBoundary F) t) (wholeDensity bare ref F (idealBoundary F) t)
    ((n+1 : ℝ)⁻¹) (by positivity) hh
  change traceDistance (FactoryControllerReturn.wholeState (hardware bare ref F service) t)
    ((controller F).matrix ⊗ₖ partialLeft (FactoryControllerReturn.wholeState (hardware bare ref F service) t)) ≤ _
  rw [actual_whole bare ref F service t]
  simpa only [div_eq_mul_inv] using h

end ScheduleLaw.Blueprint.CacheHardwareReturn
