import ServiceSourceMarginal
import FactoryEnergyTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.ServiceEnergyTelescope
open History
variable {I : Inventory} {S : Schedule I}
variable {a : Type} [Fintype a] [DecidableEq a]

theorem energy_change (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N)) (H : Mat (Fin bare.b)) (K : Mat a)
    {z : ℕ} (t : Tester S z) :
    energy ((H ⊗ₖ (1 : Mat a)+(1 : Mat (Fin bare.b)) ⊗ₖ K).submatrix e e)
      (bodyOutput (CacheServiceGates.extension bare hN e ρ) t)-
      energy ((H ⊗ₖ (1 : Mat a)+(1 : Mat (Fin bare.b)) ⊗ₖ K).submatrix e e) ρ.matrix=
      energy H (bodyOutput (CacheSourceHistory.withSource bare (ServiceSourceMarginal.source bare e ρ)) t-
        (ServiceSourceMarginal.source bare e ρ).matrix) := by
  have ho := FactoryEnergyTransport.energy_inverse e (H ⊗ₖ (1 : Mat a)+(1 : Mat (Fin bare.b)) ⊗ₖ K)
    (bodyOutput (CacheServiceGates.extension bare hN e ρ) t)
  have hi := FactoryEnergyTransport.energy_inverse e (H ⊗ₖ (1 : Mat a)+(1 : Mat (Fin bare.b)) ⊗ₖ K) ρ.matrix
  rw [← ho,← hi,energy_add,energy_add,energy_kron_one,energy_one_kron,energy_kron_one,energy_one_kron]
  have hr : partialLeft ((bodyOutput (CacheServiceGates.extension bare hN e ρ) t).submatrix e.symm e.symm)=
      partialLeft (ρ.matrix.submatrix e.symm e.symm) := CacheServiceHistory.retained bare hN e ρ t (2*S.visits+1)
  rw [hr,ServiceSourceMarginal.body bare e hN ρ t]
  change _-(energy H (ServiceSourceMarginal.source bare e ρ).matrix+_)=_
  rw [SourceFunctional.state_sub]
  ring

theorem run_same_source (e : Extension S) {z : ℕ} (t : Tester S z) (k : ℕ) :
    ScheduleLaw.run (CacheSourceHistory.withSource e e.source) t k=ScheduleLaw.run e t k := by
  rw [CacheSourceHistory.run,run_eq_history]
  rfl

theorem physical_same_source (β : ℝ) (e : Extension S) (q : Density (Fin e.b))
    {z : ℕ} (t : Tester S z) :
    physicalLinearized β (CacheSourceHistory.withSource e e.source) q t=physicalLinearized β e q t := by
  have hb : bodyOutput (CacheSourceHistory.withSource e e.source) t=bodyOutput e t := by
    unfold bodyOutput finalState
    rw [run_same_source]
  have hh : handoff (CacheSourceHistory.withSource e e.source) t=handoff e t := by
    unfold handoff
    apply Finset.sum_congr rfl
    intro v _
    rw [run_same_source,run_same_source]
    rfl
  unfold physicalLinearized
  rw [hb,hh]

end ScheduleLaw.Blueprint.ServiceEnergyTelescope
