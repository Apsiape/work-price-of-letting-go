import CircuitEnergy
import EntropyProducts
import QuantumEntropyAdapter
import RateConverse
import AbstractStrategies
import PurifiedScore

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
namespace ScheduleLaw

theorem reservoir_relative_nonnegative_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) :
    0 ≤ (engineLedger e t).relativeEntropy := by
  letI : Nonempty (Fin e.r) := ⟨⟨0,e.r_pos⟩⟩
  let ρ : Density (Fin e.r) := ⟨reservoirFinal e t,
    (reservoirFinal_density e t).1,(reservoirFinal_density e t).2⟩
  let γ : Density (Fin e.r) := ⟨gibbs β e.HR,gibbs_positive β e.HR,gibbs_trace β e.HR⟩
  exact relative_entropy_nonnegative ρ γ (gibbs_faithful β e.HR)

/-- All five fields are consequences of the concrete finite circuit. -/
theorem physical_accounting_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) : PhysicalAccountingData e where
  accounts r t := ⟨entropy_accounting_from_circuit e r t,
    reservoir_entropy_from_circuit e r t,energy_accounting_from_circuit e r t⟩
  relative_nonneg := reservoir_relative_nonnegative_from_circuit e
  correlation_nonneg := correlation_nonnegative_from_circuit e
  battery_nonneg := battery_nonnegative_from_circuit e
  battery_normalized := battery_normalized_from_circuit e

theorem whole_block_identity_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (hβ : 0 < β) (e : Engine S β) (r : ℕ) (t : Tester S r) :
    -(engineLedger e t).batteryEnergy - (engineLedger e t).controllerEnergy +
      ((engineLedger e t).controllerEntropy + (engineLedger e t).batteryEntropy) / β =
      (engineLedger e t).handoffEnergy +
        (purifiedConditionalEntropy e.extension t + (engineLedger e t).relativeEntropy +
          (engineLedger e t).totalCorrelation) / β := by
  rw [purified_conditional_entropy]
  exact whole_block_ledger (engineLedger e t) β hβ
    ((physical_accounting_from_circuit e).accounts r t)

/-- The physical finite-block bound with no accounting premise. -/
theorem finite_physical_lower_bound {I : Inventory} {S : Schedule I} {β : ℝ}
    (hβ : 0 < β) (T : Target S) (e : Engine S β) (ε : ℝ) (b : Budget)
    (service : Approximates e.extension T ε) (endpoints : MeetsBudget e b) :
    finiteCost β T ε ≤ ((nominalDebit e + b.controllerEnergy + b.absoluteTail +
      (b.controllerEntropy + b.batteryEntropy) / β : ℝ) : EReal) :=
  finite_physical_lower_bound_of_accounting hβ T e ε b service endpoints (physical_accounting_from_circuit e)

theorem regularized_converse_from_circuit {β : ℝ} (hβ : 0 < β)
    (T : TaskFamily) (d : Implementation β T) :
    regularizedCost β T ≤ implementationRate d :=
  regularized_converse_of_accounting hβ T d (fun _ => physical_accounting_from_circuit _)

theorem optimalWork_converse_from_circuit {β : ℝ} (hβ : 0 < β) (T : TaskFamily) :
    regularizedCost β T ≤ optimalWork β T :=
  optimalWork_converse_of_accounting hβ T (fun _ _ => physical_accounting_from_circuit _)

theorem regularized_converse_bits {β : ℝ} (hβ : 0 < β)
    (T : TaskFamily) (d : Implementation β T) :
    ((Real.log 2 / β : ℝ) : EReal) * Kbeta β T ≤ implementationRate d := by
  rw [bits_normalization β hβ T]
  exact regularized_converse_from_circuit hβ T d

theorem purified_regularized_converse {β : ℝ} (hβ : 0 < β)
    (T : TaskFamily) (d : Implementation β T) :
    purifiedRegularizedCost β T ≤ implementationRate d := by
  rw [← regularizedCost_eq_purified]
  exact regularized_converse_from_circuit hβ T d

theorem abstract_regularized_converse {β : ℝ} (hβ : 0 < β)
    (hcausal : FiniteCausalStinespringCompleteness) (T : AbstractTaskFamily)
    (d : Implementation β (T.realize hcausal)) :
    abstractRegularizedCost β T ≤ implementationRate d := by
  rw [← abstract_regularizedCost_realization hcausal β T]
  exact regularized_converse_from_circuit hβ (T.realize hcausal) d

end ScheduleLaw
