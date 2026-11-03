import PhaseHardwareComparison
import PhaseHardwareReturn
import PhaseStockContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.PhaseBudgetPhysical
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def energyCoeff (p : Driven S β) : ℝ :=
  2*‖PhaseStockContinuity.diagonalH p.batteryEnergy‖+2*‖p.HR.matrix‖+2*handoffBound S

def failureCoeff (p : Driven S β) : ℝ :=
  2*‖PhaseStockContinuity.diagonalH (fun j : Fin p.w => if j=p.nominalLevel then 1 else 0)‖

def tailCoeff (p : Driven S β) : ℝ :=
  2*‖PhaseStockContinuity.diagonalH (fun j => |p.batteryEnergy j-p.batteryEnergy p.nominalLevel|)‖

def coefficient (p : Driven S β) : ℝ := 2+energyCoeff p+failureCoeff p+tailCoeff p

variable (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k))
local notation "q" => PhaseHardware.hardware p hD φ Hφ G hG hlocal
local notation "idle" => IdleExtension.extension p.extension (PhaseHardware.phaseStock hD φ)

theorem return_bound (δ η : ℝ)
    (hc : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal δ)
    {z : ℕ} (t : Tester S z) (hold : Driven.controllerProductDefect p t≤η) :
    Driven.controllerProductDefect q t≤η+2*δ := by
  have hX : traceDistance (PhaseHardwareReturn.oldShape p z (finalState p.extension t))
      (p.controller.matrix ⊗ₖ partialLeft (PhaseHardwareReturn.oldShape p z (finalState p.extension t)))≤η := hold
  have hY := hc z t (2*S.visits+1) le_rfl
  rw [IdleExtension.run_idle] at hY
  exact PhaseHardwareReturn.stability p φ (finalState p.extension t) (finalState (q).extension t) η δ hX hY

theorem controller_bound (δ η : ℝ)
    (hc : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal δ)
    (hcon : ∀ k,Conserves ((q).extension.gate k)
      ((q).bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+
        (1 : Mat (Fin (q).extension.b)) ⊗ₖ payloadHamiltonian I))
    {z : ℕ} (t : Tester S z) (hold : |Driven.controllerEnergyChange p t|≤η)
    (hd : |Driven.defect p t|≤2*η) :
    |Driven.controllerEnergyChange q t|≤3*η+energyCoeff p*δ := by
  have hb := PhaseHardwareComparison.battery p hD φ Hφ G hG hlocal δ hc t
  have hr := PhaseHardwareComparison.reservoir p hD φ Hφ G hG hlocal δ hc t
  have hB := PhaseStockContinuity.diagonal_readout p.batteryEnergy
    (Driven.batteryFinal q t) (Driven.batteryFinal p t) δ hb
  have hB' : |Driven.batteryEnergyChange p t-Driven.batteryEnergyChange q t|≤
      2*‖PhaseStockContinuity.diagonalH p.batteryEnergy‖*δ := by
    have he : Driven.batteryEnergyChange p t-Driven.batteryEnergyChange q t=
        -((∑ j,p.batteryEnergy j*(Driven.batteryFinal q t j j).re)-
          (∑ j,p.batteryEnergy j*(Driven.batteryFinal p t j j).re)) := by
      unfold Driven.batteryEnergyChange Driven.batteryMeanFinal
      change ((∑ j,p.batteryEnergy j*(Driven.batteryFinal p t j j).re)-p.batteryEnergy p.initialLevel)-
        ((∑ j,p.batteryEnergy j*(Driven.batteryFinal q t j j).re)-p.batteryEnergy p.initialLevel)=_

      ring
    rw [he,abs_neg]
    exact hB
  have hR := PhaseStockContinuity.energy_sub p.HR.matrix (Driven.reservoirFinal q t)
    (Driven.reservoirFinal p t) (gibbs β p.HR) δ hr
  have hR' : |PhaseControllerRefund.reservoirChange p t-PhaseControllerRefund.reservoirChange q t|≤
      2*‖p.HR.matrix‖*δ := by
    rw [abs_sub_comm]
    exact hR
  have hH := PhaseHandoffContinuity.handoff (q).extension p.extension t δ
    (fun n hn => PhaseHardwareComparison.observer p hD φ Hφ G hG hlocal δ hc t n hn)
  have hH' : |handoff p.extension t-handoff (q).extension t|≤2*handoffBound S*δ := by
    rw [abs_sub_comm]
    exact hH
  have h := PhaseControllerRefund.bound p q hcon t η
    (2*‖PhaseStockContinuity.diagonalH p.batteryEnergy‖*δ) (2*‖p.HR.matrix‖*δ)
    (2*handoffBound S*δ) hold hd hB' hR' hH'
  calc _ ≤ _ := h
       _ = _ := by dsimp only [energyCoeff]; ring

theorem failure_bound (δ η : ℝ)
    (hc : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal δ)
    {z : ℕ} (t : Tester S z) (hold : 1-(Driven.batteryFinal p t p.nominalLevel p.nominalLevel).re≤η) :
    1-(Driven.batteryFinal q t (q).nominalLevel (q).nominalLevel).re≤η+failureCoeff p*δ := by
  have h := PhaseStockContinuity.level p.nominalLevel (Driven.batteryFinal q t) (Driven.batteryFinal p t) δ
    (PhaseHardwareComparison.battery p hD φ Hφ G hG hlocal δ hc t)
  have hh := (abs_le.mp h).1
  change 1-(Driven.batteryFinal q t p.nominalLevel p.nominalLevel).re≤η+(2*‖PhaseStockContinuity.diagonalH (fun j : Fin p.w => if j=p.nominalLevel then 1 else 0)‖)*δ
  linarith

theorem tail_bound (δ η : ℝ)
    (hc : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal δ)
    {z : ℕ} (t : Tester S z) (hold : Driven.batteryAbsoluteTail p t≤η) :
    Driven.batteryAbsoluteTail q t≤η+tailCoeff p*δ := by
  have h := PhaseStockContinuity.diagonal_readout (fun j => |p.batteryEnergy j-p.batteryEnergy p.nominalLevel|)
    (Driven.batteryFinal q t) (Driven.batteryFinal p t) δ
    (PhaseHardwareComparison.battery p hD φ Hφ G hG hlocal δ hc t)
  have hh := (abs_le.mp h).2
  change Driven.batteryAbsoluteTail q t-Driven.batteryAbsoluteTail p t≤tailCoeff p*δ at hh
  linarith

end ScheduleLaw.Blueprint.PhaseBudgetPhysical
