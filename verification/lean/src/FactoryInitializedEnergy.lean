import FactoryPumpMarginals
import FactoryPreparedSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryInitializedEnergy
open History FactoryRegisters FactoryRegisterOutput FactoryPhysicalHamiltonian

variable {b c e t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype e] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq e]
  [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

/-- Full initialized physical energy telescope, retaining every failed column
and all retired stocks. The preparation and flat code are the actual local runs. -/
theorem circuit_ledger (s : c ≃ b × e)
    (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4) (x1 x2 x4 Eg Ecode : ℝ)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V) (hu4 : IsUnitary U4)
    (hc1 : Conserves U1 (sumH H (sumH (work x1) H1)))
    (hc2 : Conserves U2 (sumH (0 : Mat c) (sumH (work x2) H2)))
    (hc4 : Conserves U4 (sumH (0 : Mat c) (sumH (work x4) H4))) :
    let K := hamiltonian (c:=c) H H1 H2 H4 x1 x2 (Eg-Ecode) x4
    let ρ := FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh
    energy K (evolve (circuit s U1 U2 V U4) ρ)-energy K ρ =
      (energy H (marginal batchFrame (evolve (circuit s U1 U2 V U4) ρ))-Ecode) +
        (Eg-energy H (partialRight (evolve U1
          (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix))))) := by
  dsimp only
  let ρ := FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh
  let σ := evolve (FactoryPlacement.place resetFrame V)
    (evolve (FactoryPlacement.place secondFrame U2) (evolve (FactoryPlacement.place firstFrame U1) ρ))
  have ht : σ.trace=1 := evolve_trace_one _ _ (FactoryPlacement.unitary _ _ hv)
    (evolve_trace_one _ _ (FactoryPlacement.unitary _ _ hu2)
      (evolve_trace_one _ _ (FactoryPlacement.unitary _ _ hu1)
        (FactoryInitializer.normalized code batch γ1 γ2 γ4 fresh)))
  have hz : FactoryFlagEffects.success (FactoryRegisterFlags.flag 2) σ=0 := by
    dsimp only [σ]
    rw [FactoryRegisterFlags.decoder_success 2 V hv,
      FactoryRegisterFlags.second_success 2 (by decide) U2 hu2,
      FactoryRegisterFlags.first_success 2 (by decide) U1 hu1]
    exact FactoryInitializedFlags.third_zero code batch γ1 γ2 γ4 fresh
  have hfinal : marginal batchFrame (evolve (circuit s U1 U2 V U4) ρ)=
      marginal (FactorySwapOutput.codingFrame s) σ := by
    simp only [circuit,evolve_mul]
    rw [batch_after_reset,batch_after_fourth U4 hu4,FactorySwapOutput.batch_after_swap]
  have hprep : marginal batchFrame σ=partialRight
      (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix))) := by
    dsimp only [σ]
    rw [FactoryPreparedSupport.batch_after_decoder V hv,
      FactoryPreparedSupport.batch_after_second U2 hu2,FactoryPreparedSupport.batch_from_first]
    change partialRight (partialRight ((evolve (FactoryPlacement.place firstFrame U1) ρ).submatrix
      firstFrame.symm firstFrame.symm)) = _
    rw [FactoryPlacement.operated_marginal]
    dsimp only [ρ]
    exact congrArg (fun A => partialRight (evolve U1 A))
      (FactoryInitializedFlags.first_stock code batch γ1 γ2 γ4 fresh)
  have hpump := FactoryPhysicalPump.pump_change s H H1 H2 H4 x1 x2 x4 Eg Ecode σ ht hz
  dsimp only at hpump
  rw [FactoryPumpMarginals.code_marginal,FactoryPumpMarginals.batch_marginal,
    ← hfinal,hprep] at hpump
  exact (circuit_change s H H1 H2 H4 x1 x2 (Eg-Ecode) x4 U1 U2 V U4
    hu1 hu2 hv hu4 hc1 hc2 hc4 ρ).trans hpump

end ScheduleLaw.Blueprint.FactoryInitializedEnergy
