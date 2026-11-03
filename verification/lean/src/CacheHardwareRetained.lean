import CacheHardwareHistory
import CacheTerminalReset
import FactoryPumpMarginals
import FactoryWorkPacking

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHardwareRetained
open History CacheHardware CacheHardwareHistory FactoryRegisterOutput
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def sourceFrame (F : Formation β τ q (n+1)) :
    CacheFlaggedCircuit.Physical F ≃ Fin d × ActiveRest F where
  toFun
    | (flags,batch,helper) =>
      let b := CacheBatchSplit.split n batch
      (b.1,flags,b.2,helper)
  invFun | (b,flags,cache,helper) => (flags,(CacheBatchSplit.split n).symm (b,cache),helper)
  left_inv z := by rcases z with ⟨flags,batch,helper⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨b,flags,cache,helper⟩; simp only [Equiv.apply_symm_apply]

def activeReadout (F : Formation β τ q (n+1)) (M : Mat (Fin (size F))) : Mat (ActiveRest F) :=
  partialRight (partialLeft (M.submatrix ((bodyFrame F).trans (activeFrame F)).symm
    ((bodyFrame F).trans (activeFrame F)).symm))

theorem reset_readout (F : Formation β τ q (n+1)) (M : Mat (Fin (size F))) :
    activeReadout F (evolve (reset F) M)=activeReadout F M := by
  let E := (bodyFrame F).trans (activeFrame F)
  have hreset : reset F = ((FactoryReset.swap (a:=Fin d) (b:=ActiveRest F)).permMatrix ℂ).submatrix E E := rfl
  have he : (evolve (reset F) M).submatrix E.symm E.symm =
      evolve ((FactoryReset.swap (a:=Fin d) (b:=ActiveRest F)).permMatrix ℂ)
        (M.submatrix E.symm E.symm) := by
    rw [← evolve_submatrix_equiv E.symm,hreset]
    congr 1
    ext i j
    simp only [submatrix_apply,Equiv.apply_symm_apply]
  change partialRight (partialLeft ((evolve (reset F) M).submatrix E.symm E.symm)) = _
  rw [he,Recorder.permutation_evolve]
  ext i j
  simp only [activeReadout,partialRight,partialLeft,submatrix_apply,FactoryReset.swap,Equiv.coe_fn_mk]
  exact Finset.sum_comm

variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1))

theorem active_output {z : ℕ} (t : Tester S z) :
    activeReadout F (bodyOutput (CacheHardware.extension bare ref F) t) =
      activeReadout F (prepared bare ref F).matrix := by
  change activeReadout F (bodyOutput
    (finalBodyContact (CacheServiceGates.prepare (base bare ref F) (preparation F)
      (preparation_unitary F)) (reset F) (reset_unitary F)) t) = _
  rw [finalBodyContact_bodyOutput,reset_readout,CachePreparationHistory.body_output]
  have h := CacheServiceHistory.retained bare (size_pos bare.b_pos F)
    ((bodyFrame F).trans (activeFrame F)) (prepared bare ref F) t (2*S.visits+1)
  exact congrArg partialRight h

theorem prepared_readout (hβ : β≠0) (hq : ref.matrix.PosDef) :
    activeReadout F (prepared bare ref F).matrix =
      partialLeft ((CacheMixture.output F).submatrix (sourceFrame F).symm (sourceFrame F).symm) := by
  rw [prepared_eq bare ref F hβ hq]
  ext i j
  simp only [activeReadout,partialRight,partialLeft,submatrix_apply,Equiv.symm_trans_apply,
    Equiv.apply_symm_apply,activeFrame,sourceFrame,Equiv.coe_fn_symm_mk,kroneckerMap_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have htr : ∑ k,ref.matrix k k=1 := ref.normalized
  rw [htr]
  simp only [mul_one]

theorem active_output_eq (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    activeReadout F (bodyOutput (CacheHardware.extension bare ref F) t) =
      partialLeft ((CacheMixture.output F).submatrix (sourceFrame F).symm (sourceFrame F).symm) := by
  rw [active_output bare ref F t,prepared_readout bare ref F hβ hq]

end ScheduleLaw.Blueprint.CacheHardwareRetained
