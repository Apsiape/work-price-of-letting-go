import CacheHardwareHistory
import CacheResetConservation
import ServiceEnergyTelescope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CachePhysicalDefect
open History CacheHardware CacheHardwareHistory
variable {I : Inventory} {S : Schedule I} {n : ℕ} {β : ℝ}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem preparation_energy (hβ : β≠0) (hq : ref.matrix.PosDef) :
    energy (CachePhysicalHamiltonian.packed F service)
      ((prepared bare ref F).matrix-(CacheHardware.source bare.b_pos F).matrix)=
        -service+Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ) := by
  have hp : (prepared bare ref F).matrix.submatrix (bodyFrame F).symm (bodyFrame F).symm=
      CacheMixture.output F ⊗ₖ ref.matrix := by
    rw [prepared_eq bare ref F hβ hq]
    simp only [submatrix_submatrix,Equiv.self_comp_symm,submatrix_id_id]
  have hi := CacheHardwareStock.initialized bare.b_pos F hβ hq
  have ht : (CacheMixture.output F).trace=1 := by
    rw [CacheMixture.output,evolve_trace _ _ (CacheFlaggedCircuit.circuit_unitary F)]
    exact (CacheMixture.input_density F).2
  have he1 := energy_reindex (bodyFrame F).symm (CachePhysicalHamiltonian.packed F service)
    (prepared bare ref F).matrix
  have he0 := energy_reindex (bodyFrame F).symm (CachePhysicalHamiltonian.packed F service)
    (CacheHardware.source bare.b_pos F).matrix
  rw [CachePhysicalHamiltonian.packed_physical,hp,energy_add,energy_kron_one,energy_one_kron,
    partialRight_kron,partialLeft_kron,ref.normalized,ht,one_smul,one_smul] at he1
  rw [CachePhysicalHamiltonian.packed_physical,hi,energy_add,energy_kron_one,energy_one_kron,
    partialRight_kron,partialLeft_kron,ref.normalized,(CacheMixture.input_density F).2,one_smul,one_smul] at he0
  have hm := CachePreparationEnergy.mixture_change F service hβ hq
  rw [SourceFunctional.state_sub] at hm ⊢
  linarith

theorem exact_ledger (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    Driven.defect (hardware bare ref F service) t=
      physicalLinearized β (CacheSourceHistory.withSource bare
        (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (prepared bare ref F))) ref t-
      service+Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ) := by
  let E := (bodyFrame F).trans (activeFrame F)
  let ρ := prepared bare ref F
  let X := CacheServiceGates.extension bare (size_pos bare.b_pos F) E ρ
  let H := tangentHamiltonian β ref
  let K := CachePhysicalHamiltonian.active F service ⊗ₖ (1 : Mat (Fin bare.b))+
    (1 : Mat (ActiveRest F)) ⊗ₖ H
  have hpack : CachePhysicalHamiltonian.packed F service=
      (H ⊗ₖ (1 : Mat (ActiveRest F × Fin bare.b))+
        (1 : Mat (Fin bare.b)) ⊗ₖ K).submatrix E E := by
    ext i j
    have h := congrArg (fun M => M (E i) (E j)) (CachePhysicalHamiltonian.active_packed F service)
    simp only [submatrix_apply,Equiv.symm_apply_apply,CacheTerminalReset.hamiltonian,H,K,
      kroneckerMap_apply,Matrix.add_apply,Matrix.one_apply] at h ⊢
    by_cases heq : (E i).2=(E j).2
    · simpa only [E,Equiv.symm_apply_apply,heq,if_true] using h
    · simpa only [E,Equiv.symm_apply_apply,heq,if_false] using h
  have he := ServiceEnergyTelescope.energy_change bare (size_pos bare.b_pos F) E ρ H K t
  rw [← hpack] at he
  have hh := ServiceSourceMarginal.handoff bare E (size_pos bare.b_pos F) ρ t
  have hp := preparation_energy bare ref F service hβ hq
  rw [SourceFunctional.state_sub] at hp
  unfold Driven.defect
  rw [SourceFunctional.state_sub,← add_sub_assoc]
  change handoff (finalBodyContact (CacheServiceGates.prepare (base bare ref F) (preparation F)
    (preparation_unitary F)) (reset F) (reset_unitary F)) t+
    energy (CachePhysicalHamiltonian.packed F service)
      (bodyOutput (finalBodyContact (CacheServiceGates.prepare (base bare ref F) (preparation F)
        (preparation_unitary F)) (reset F) (reset_unitary F)) t)-_= _
  rw [finalBodyContact_handoff,finalBodyContact_bodyOutput,
    CachePreparationHistory.handoff,CachePreparationHistory.body_output]
  change handoff X t+energy (CachePhysicalHamiltonian.packed F service) (evolve (reset F) (bodyOutput X t))-
    energy (CachePhysicalHamiltonian.packed F service) (CacheHardware.source bare.b_pos F).matrix=_
  rw [energy_conserved _ _ _ (CachePhysicalHamiltonian.reset_conserves F service)]
  unfold physicalLinearized
  change handoff X t+energy (CachePhysicalHamiltonian.packed F service) (bodyOutput X t)-
    energy (CachePhysicalHamiltonian.packed F service) (CacheHardware.source bare.b_pos F).matrix=
      handoff (CacheSourceHistory.withSource bare (ServiceSourceMarginal.source bare E ρ)) t+
      energy H (bodyOutput (CacheSourceHistory.withSource bare (ServiceSourceMarginal.source bare E ρ)) t-
        (ServiceSourceMarginal.source bare E ρ).matrix)-service+Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ)
  linarith

end ScheduleLaw.Blueprint.CachePhysicalDefect
