import PhaseHandoffContinuity
import PhaseControllerRefund

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.PhaseStockContinuity
variable {a : Type} [Fintype a] [DecidableEq a]

def diagonalH (E : a → ℝ) : Mat a := diagonal (fun j => (E j : ℂ))

theorem diagonal_readout (E : a → ℝ) (X Y : Mat a) (δ : ℝ) (h : traceDistance X Y≤δ) :
    |(∑ j,E j*(X j j).re)-(∑ j,E j*(Y j j).re)|≤2*‖diagonalH E‖*δ := by
  rw [← battery_diagonal_energy,← battery_diagonal_energy]
  exact (FactoryEnergy.energy_distance _ _ _).trans (mul_le_mul_of_nonneg_left h (by positivity))

theorem level (j : a) (X Y : Mat a) (δ : ℝ) (h : traceDistance X Y≤δ) :
    |(X j j).re-(Y j j).re|≤2*‖diagonalH (fun i => if i=j then 1 else 0)‖*δ := by
  simpa only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using
    diagonal_readout (fun i => if i=j then 1 else 0) X Y δ h

theorem energy_sub (H X Y A : Mat a) (δ : ℝ) (h : traceDistance X Y≤δ) :
    |energy H (X-A)-energy H (Y-A)|≤2*‖H‖*δ := by
  have he : energy H (X-A)-energy H (Y-A)=energy H X-energy H Y := by
    rw [SourceFunctional.state_sub,SourceFunctional.state_sub]
    ring
  rw [he]
  exact (FactoryEnergy.energy_distance H X Y).trans (mul_le_mul_of_nonneg_left h (by positivity))

end ScheduleLaw.Blueprint.PhaseStockContinuity
