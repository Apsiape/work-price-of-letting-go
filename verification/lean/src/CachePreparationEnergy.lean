import CacheFactoryEnergy
import CacheHardware
import FactoryPlacement
import SourceFunctional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CachePreparationEnergy
open History CacheFlaggedCircuit
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def flagEnergy (F : Formation β τ q (n+1)) (service : ℝ) (z : Flags n) : ℝ :=
  CacheClockAdvance.clockEnergy n F.debit z.1+
    (if z.2.1=1 then -(F.debit+service) else 0)+
      (if z.2.2=1 then (n+1 : ℝ)*F.debit else 0)

def physical (F : Formation β τ q (n+1)) (service : ℝ) : Mat (Physical F) :=
  diagonal (fun z => (flagEnergy F service z : ℂ)) ⊗ₖ
    (1 : Mat (CacheFactoryBody.Batch d (n+1) × CacheFactoryBody.Rest F))+
      (1 : Mat (Flags n)) ⊗ₖ CacheFactoryEnergy.physical F

theorem level_trace {a : Type} [Fintype a] [DecidableEq a] (j : a) : (level j).trace=1 := by
  rw [level,pureMatrix_trace]
  simp

theorem sector_energy (F : Formation β τ q (n+1)) (service : ℝ) (j : Flags n)
    (M : Mat (CacheFactoryBody.Batch d (n+1) × CacheFactoryBody.Rest F)) (hM : M.trace=1) :
    energy (physical F service) (level j ⊗ₖ M)=flagEnergy F service j+energy (CacheFactoryEnergy.physical F) M := by
  rw [physical,energy_add,energy_kron_one,energy_one_kron,partialRight_kron,partialLeft_kron,
    hM,level_trace,one_smul,one_smul]
  congr 1
  simp [energy,Matrix.trace,Matrix.diagonal_mul,level,pureMatrix]

theorem input_trace (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    (W2.tensorFamily (CacheCellShift.sourceSector τ q n j) ⊗ₖ CacheFactoryBody.helper F).trace=1 := by
  rw [trace_kronecker,W2.tensorFamily_trace,(CacheMixture.helper_density F).2,one_mul]

theorem result_trace (F : Formation β τ q (n+1)) : (CacheFactoryBody.result F).trace=1 := by
  rw [CacheFactoryBody.result,submatrix_trace_equiv]
  exact (bodyOutput_density _ _).2

theorem body_rotation (F : Formation β τ q (n+1)) :
    Conserves (((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ) ⊗ₖ
      (1 : Mat (CacheFactoryBody.Rest F))) (CacheFactoryEnergy.physical F) := by
  exact FactoryPlacement.conserves (Equiv.refl _)
    ((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ)
    (tensorHamiltonian (tangentHamiltonian β q) (n+1)) (CacheFactoryEnergy.helper F)
    (Recorder.permutation_unitary _) (CacheCellShift.conserving (finRotate (n+1)).symm _)

theorem rotation_conserves (F : Formation β τ q (n+1)) (service : ℝ) :
    Conserves (rotation F) (physical F service) := by
  have hb := body_rotation F
  have hu : IsUnitary (((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ) ⊗ₖ
      (1 : Mat (CacheFactoryBody.Rest F))) := unitary_kron (Recorder.permutation_unitary _)
        (by constructor <;> simp)
  have hp := (Recorder.permutation_unitary (CacheCellShift.coordinates (a:=Fin d) ((finRotate (n+1)).symm))).1
  unfold Conserves at hb ⊢
  simp only [conjTranspose_kronecker,conjTranspose_one] at hb
  simp only [CacheFlaggedCircuit.rotation,physical,conjTranspose_kronecker,conjTranspose_one,mul_add,add_mul,
    ← mul_kronecker_mul,mul_one,one_mul,hp,one_kronecker_one,hb]

theorem flag_change (F : Formation β τ q (n+1)) (service : ℝ) (j : Fin (n+1)) :
    flagEnergy F service (CacheClockAdvance.target n j)-flagEnergy F service (CacheClockAdvance.source n j) = -service := by
  have h := CacheWorkLedger.pump_change F service j F.hardware.initialLevel
  by_cases hj : j=0 <;>
    simp [flagEnergy,CacheClockAdvance.target,CacheClockAdvance.source,
      CacheWorkLedger.energy,CacheWorkLedger.helperEnergy,hj] at * <;> linarith

theorem sector_change (F : Formation β τ q (n+1)) (service : ℝ) (hβ : β≠0) (hq : q.matrix.PosDef)
    (j : Fin (n+1)) :
    energy (physical F service) (evolve (circuit F) (inputSector F j))-
      energy (physical F service) (inputSector F j)=
        -service+(if j=0 then Driven.defect F.hardware (idleTester F.schedule) else 0) := by
  rw [circuit,evolve_mul,evolve_mul,energy_conserved _ _ _ (rotation_conserves F service),
    pump_sector,factory,controlled_sector]
  have hflag := flag_change F service j
  by_cases hj : j=0
  · subst j
    simp only [CacheClockAdvance.target,if_true]
    rw [CacheFlaggedCircuit.boundary_input F,CacheFactoryBody.run F hβ hq,inputSector,
      sector_energy F service _ _ (result_trace F),sector_energy F service _ _ (input_trace F 0)]
    have he := CacheFactoryEnergy.initialized_defect F hβ hq
    rw [show energy (CacheFactoryEnergy.physical F)
        (CacheFactoryBody.result F-tensorPower q.matrix (n+1) ⊗ₖ CacheFactoryBody.helper F)=
        energy (CacheFactoryEnergy.physical F) (CacheFactoryBody.result F)-
        energy (CacheFactoryEnergy.physical F) (tensorPower q.matrix (n+1) ⊗ₖ CacheFactoryBody.helper F) from
          (energyLinear _).map_sub _ _] at he
    rw [CacheFlaggedCircuit.boundary_input F]
    simp only [CacheClockAdvance.target,if_true] at hflag
    linarith
  · simp only [CacheClockAdvance.target,if_neg hj,Fin.zero_ne_one,if_false]
    simp only [evolve,conjTranspose_one,one_mul,mul_one]
    rw [inputSector,sector_energy F service _ _ (input_trace F j),
      sector_energy F service _ _ (input_trace F j)]
    simp only [CacheClockAdvance.target,if_neg hj] at hflag
    linarith

theorem mixture_change (F : Formation β τ q (n+1)) (service : ℝ) (hβ : β≠0) (hq : q.matrix.PosDef) :
    energy (physical F service) (CacheMixture.output F-CacheMixture.input F)=
      -service+Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ) := by
  let L := energyLinear (physical F service)
  change L (CacheMixture.output F-CacheMixture.input F)=_
  rw [map_sub,CacheMixture.run_mixture,CacheMixture.input]
  simp only [map_smul,map_sum,smul_eq_mul]
  rw [← mul_sub,← Finset.sum_sub_distrib]
  change (n+1 : ℝ)⁻¹ * ∑ j : Fin (n+1),
    (energy (physical F service) (evolve (circuit F) (inputSector F j))-
      energy (physical F service) (inputSector F j)) = _
  simp_rw [sector_change F service hβ hq]
  simp [Finset.sum_add_distrib]
  field_simp

end ScheduleLaw.Blueprint.CachePreparationEnergy
