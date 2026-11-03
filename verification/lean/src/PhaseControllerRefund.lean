import PhaseEnergyRefund
import FactoryDrivenEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseControllerRefund
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def reservoirChange (p : Driven S β) {z : ℕ} (t : Tester S z) : ℝ :=
  energy p.HR.matrix (Driven.reservoirFinal p t-gibbs β p.HR)

/-- Conservation refunds the complete enlarged controller, including the
nonzero phase Hamiltonian, through only the unchanged physical stocks. -/
theorem exact_ledger (p q : Driven S β)
    (hcon : ∀ k,Conserves (q.extension.gate k)
      (q.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+(1 : Mat (Fin q.extension.b)) ⊗ₖ payloadHamiltonian I))
    {z : ℕ} (t : Tester S z) :
    Driven.controllerEnergyChange q t=Driven.controllerEnergyChange p t-Driven.defect p t+
      (Driven.batteryEnergyChange p t-Driven.batteryEnergyChange q t)+
      (reservoirChange p t-reservoirChange q t)+(handoff p.extension t-handoff q.extension t) := by
  have hp := FactoryDrivenEnergy.defect_accounting p t
  have hq := FactoryDrivenEnergy.defect_accounting q t
  have h0 := PhaseEnergyRefund.conserving_defect_zero q hcon t
  change Driven.defect p t=handoff p.extension t+Driven.controllerEnergyChange p t+
    Driven.batteryEnergyChange p t+reservoirChange p t at hp
  change Driven.defect q t=handoff q.extension t+Driven.controllerEnergyChange q t+
    Driven.batteryEnergyChange q t+reservoirChange q t at hq
  linarith

theorem bound (p q : Driven S β)
    (hcon : ∀ k,Conserves (q.extension.gate k)
      (q.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+(1 : Mat (Fin q.extension.b)) ⊗ₖ payloadHamiltonian I))
    {z : ℕ} (t : Tester S z) (η eB eR eH : ℝ)
    (hC : |Driven.controllerEnergyChange p t|≤η) (hd : |Driven.defect p t|≤2*η)
    (hB : |Driven.batteryEnergyChange p t-Driven.batteryEnergyChange q t|≤eB)
    (hR : |reservoirChange p t-reservoirChange q t|≤eR)
    (hH : |handoff p.extension t-handoff q.extension t|≤eH) :
    |Driven.controllerEnergyChange q t|≤3*η+eB+eR+eH := by
  have he := exact_ledger p q hcon t
  rcases abs_le.mp hC with ⟨hC1,hC2⟩
  rcases abs_le.mp hd with ⟨hd1,hd2⟩
  rcases abs_le.mp hB with ⟨hB1,hB2⟩
  rcases abs_le.mp hR with ⟨hR1,hR2⟩
  rcases abs_le.mp hH with ⟨hH1,hH2⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ScheduleLaw.Blueprint.PhaseControllerRefund
