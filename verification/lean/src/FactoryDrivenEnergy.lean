import FactoryDriven
import FactoryPreparedEnergy
import EmptyContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryDrivenEnergy
open History

theorem bodyEnergy_decomposition {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) (ρ : Mat (Fin e.extension.b)) :
    energy e.bodyHamiltonian ρ =
      energy e.HC.matrix (partialRight (ρ.submatrix e.split.symm e.split.symm)) +
        energy (diagonal fun j => (e.batteryEnergy j : ℂ))
          (partialRight (partialLeft (ρ.submatrix e.split.symm e.split.symm))) +
        energy e.HR.matrix (partialLeft (partialLeft (ρ.submatrix e.split.symm e.split.symm))) := by
  rw [← energy_reindex e.split.symm e.bodyHamiltonian ρ]
  have hh : e.bodyHamiltonian.submatrix e.split.symm e.split.symm =
      e.HC.matrix ⊗ₖ (1 : Mat (Fin e.w × Fin e.r)) +
        (1 : Mat (Fin e.c)) ⊗ₖ
          ((diagonal fun j => (e.batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin e.r)) +
            (1 : Mat (Fin e.w)) ⊗ₖ e.HR.matrix) := by
    ext i j
    simp [Driven.bodyHamiltonian,submatrix_apply]
  rw [hh,energy_add,energy_kron_one,energy_one_kron,energy_add,
    energy_kron_one,energy_one_kron]
  ring

theorem bodyEnergy_final {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) :
    energy e.bodyHamiltonian (bodyOutput e.extension t) =
      energy e.HC.matrix (Driven.controllerFinal e t) + Driven.batteryMeanFinal e t +
        energy e.HR.matrix (Driven.reservoirFinal e t) := by
  rw [bodyEnergy_decomposition,battery_diagonal_energy]
  rfl

theorem bodyEnergy_initial {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) : energy e.bodyHamiltonian e.extension.source.matrix =
      energy e.HC.matrix e.controller.matrix + e.batteryEnergy e.initialLevel +
        energy e.HR.matrix (gibbs β e.HR) := by
  letI : Nonempty (Fin e.r) := ⟨⟨0,e.r_pos⟩⟩
  let P : Mat (Fin e.w) := pureMatrix (fun i => if i = e.initialLevel then 1 else 0)
  have hP : P.trace = 1 := by
    dsimp [P]
    rw [pureMatrix_trace]
    simp
  have hp : e.extension.source.matrix.submatrix e.split.symm e.split.symm =
      e.controller.matrix ⊗ₖ (P ⊗ₖ gibbs β e.HR) := by
    rw [e.source_product]
    ext i j
    simp [submatrix_apply,P]
  rw [bodyEnergy_decomposition,hp]
  simp only [partialRight_kron,partialLeft_kron,trace_kronecker,hP,gibbs_trace,
    e.controller.normalized,mul_one,one_smul]
  have hPE : energy (diagonal fun j => (e.batteryEnergy j : ℂ)) P =
      e.batteryEnergy e.initialLevel := by
    rw [battery_diagonal_energy]
    simp [P,pureMatrix,mul_ite,ite_mul,apply_ite]
  rw [hPE]

/-- The original full initialized defect accounts for every controller,
battery and reservoir register, before imposing conservation. -/
theorem defect_accounting {I : Inventory} {S : Schedule I} {β : ℝ}
    (p : Driven S β) {z : ℕ} (t : Tester S z) :
    Driven.defect p t=handoff p.extension t + Driven.controllerEnergyChange p t +
      Driven.batteryEnergyChange p t +
        energy p.HR.matrix (Driven.reservoirFinal p t-gibbs β p.HR) := by
  unfold Driven.defect
  have he : energy p.bodyHamiltonian (bodyOutput p.extension t-p.extension.source.matrix)=
      energy p.bodyHamiltonian (bodyOutput p.extension t)-energy p.bodyHamiltonian p.extension.source.matrix := by
    simp only [energy,mul_sub,trace_sub,Complex.sub_re]
  rw [he,bodyEnergy_final,bodyEnergy_initial]
  simp only [Driven.controllerEnergyChange,Driven.batteryEnergyChange,energy,mul_sub,trace_sub,Complex.sub_re]
  ring

theorem defect_empty {I : Inventory} {S : Schedule I} {β : ℝ}
    (p : Driven S β) (hS : S.visits=0) {z : ℕ} (t : Tester S z) :
    Driven.defect p t=Driven.controllerEnergyChange p t + Driven.batteryEnergyChange p t +
      energy p.HR.matrix (Driven.reservoirFinal p t-gibbs β p.HR) := by
  rw [defect_accounting,handoff_zero_visits p.extension hS t,zero_add]

end ScheduleLaw.Blueprint.FactoryDrivenEnergy
