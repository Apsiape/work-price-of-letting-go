import FactoryDrivenEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryReservoirEnergy
open History

variable {d m : ℕ} {β : ℝ} {τ q : Density (Fin d)}

theorem body_independent (F : Formation β τ q m) {z : ℕ} (t : Tester F.schedule z) :
    bodyOutput F.hardware.extension t=bodyOutput F.hardware.extension (idleTester F.schedule) := by
  rw [bodyOutput_zero_visits F.hardware.extension F.empty,
    bodyOutput_zero_visits F.hardware.extension F.empty]

theorem reservoir_independent (F : Formation β τ q m) {z : ℕ} (t : Tester F.schedule z) :
    Driven.reservoirFinal F.hardware t=Driven.reservoirFinal F.hardware (idleTester F.schedule) := by
  unfold Driven.reservoirFinal Driven.batteryReservoirFinal
  rw [body_independent F t]

theorem batch_output (F : Formation β τ q m) {z : ℕ} (t : Tester F.schedule z) :
    partialRight ((Driven.reservoirFinal F.hardware t).submatrix
      F.reservoirSplit.symm F.reservoirSplit.symm)=F.output := by
  rw [reservoir_independent F t]
  rfl

theorem reservoir_energy (F : Formation β τ q m) (ρ : Mat (Fin F.hardware.r)) :
    energy F.hardware.HR.matrix ρ=
      energy (tensorHamiltonian (tangentHamiltonian β q) m)
        (partialRight (ρ.submatrix F.reservoirSplit.symm F.reservoirSplit.symm)) +
      energy F.auxiliaryHamiltonian.matrix
        (partialLeft (ρ.submatrix F.reservoirSplit.symm F.reservoirSplit.symm)) := by
  rw [← energy_reindex F.reservoirSplit.symm,F.reservoirHamiltonian,
    energy_add,energy_kron_one,energy_one_kron]

def auxiliaryFinal (F : Formation β τ q m) {z : ℕ} (t : Tester F.schedule z) : Mat (Fin F.aux) :=
  partialLeft ((Driven.reservoirFinal F.hardware t).submatrix
    F.reservoirSplit.symm F.reservoirSplit.symm)

def auxiliaryInitial (F : Formation β τ q m) : Mat (Fin F.aux) :=
  partialLeft ((gibbs β F.hardware.HR).submatrix F.reservoirSplit.symm F.reservoirSplit.symm)

/-- Exact original initialized-defect accounting. The auxiliary term retains
all converter baths, fresh reset stock and coding residue; no register or
failed column is omitted. Every tester has the same emitted batch. -/
theorem defect_accounting (F : Formation β τ q m) {z : ℕ} (t : Tester F.schedule z) :
    Driven.defect F.hardware t=
      Driven.controllerEnergyChange F.hardware t + Driven.batteryEnergyChange F.hardware t +
      (energy (tensorHamiltonian (tangentHamiltonian β q) m) F.output -
        energy (tensorHamiltonian (tangentHamiltonian β q) m) (tensorPower q.matrix m)) +
      (energy F.auxiliaryHamiltonian.matrix (auxiliaryFinal F t) -
        energy F.auxiliaryHamiltonian.matrix (auxiliaryInitial F)) := by
  rw [FactoryDrivenEnergy.defect_empty F.hardware F.empty t]
  have he : energy F.hardware.HR.matrix (Driven.reservoirFinal F.hardware t-gibbs β F.hardware.HR)=
      energy F.hardware.HR.matrix (Driven.reservoirFinal F.hardware t)-
        energy F.hardware.HR.matrix (gibbs β F.hardware.HR) := by
    simp only [energy,mul_sub,trace_sub,Complex.sub_re]
  rw [he,reservoir_energy,reservoir_energy,batch_output F t,F.initial_batch]
  dsimp only [auxiliaryFinal,auxiliaryInitial]
  ring

end ScheduleLaw.Blueprint.FactoryReservoirEnergy
