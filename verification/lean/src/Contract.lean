import Foundations

set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker Topology ComplexOrder
namespace ScheduleLaw

/-- One fixed finite physical engine. The body is explicitly C × W × R.
All workspace belongs to C; R denotes all Gibbs stocks, including used stocks.
The battery is diagonal in its declared mechanical basis. -/
structure Engine {I : Inventory} (S : Schedule I) (β : ℝ) where
  extension : Extension S
  c : ℕ
  w : ℕ
  r : ℕ
  c_pos : 0 < c
  w_pos : 0 < w
  r_pos : 0 < r
  split : Fin extension.b ≃ Fin c × (Fin w × Fin r)
  controller : Density (Fin c)
  HC : Hamiltonian (Fin c)
  HR : Hamiltonian (Fin r)
  batteryEnergy : Fin w → ℝ
  initialLevel : Fin w
  nominalLevel : Fin w
  /-- Declared startup free-energy capital. No rate bound is imposed. -/
  capital : ℝ
  source_product : extension.source.matrix =
    (controller.matrix ⊗ₖ
      (pureMatrix (fun j => if j = initialLevel then 1 else 0) ⊗ₖ gibbs β HR)).submatrix
        split split
  gate_conserves : ∀ k, Conserves (extension.gate k)
    (((HC.matrix ⊗ₖ (1 : Mat (Fin w × Fin r)) +
       (1 : Mat (Fin c)) ⊗ₖ
         ((diagonal fun j => (batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin r)) +
           (1 : Mat (Fin w)) ⊗ₖ HR.matrix)).submatrix split split) ⊗ₖ
      (1 : Mat (Payload I)) +
      (1 : Mat (Fin extension.b)) ⊗ₖ payloadHamiltonian I)

def nominalDebit {I : Inventory} {S : Schedule I} {β : ℝ} (e : Engine S β) : ℝ :=
  e.batteryEnergy e.initialLevel - e.batteryEnergy e.nominalLevel

def controllerFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : Mat (Fin e.c) :=
  partialRight ((bodyOutput e.extension t).submatrix e.split.symm e.split.symm)

def batteryReservoirFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : Mat (Fin e.w × Fin e.r) :=
  partialLeft ((bodyOutput e.extension t).submatrix e.split.symm e.split.symm)

def batteryFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :=
  partialRight (batteryReservoirFinal e t)

def reservoirFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :=
  partialLeft (batteryReservoirFinal e t)

def controllerEnergyChange {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : ℝ :=
  energy e.HC.matrix (controllerFinal e t) - energy e.HC.matrix e.controller.matrix

def controllerEntropyChange {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : ℝ :=
  entropy (controllerFinal e t) - entropy e.controller.matrix

def batteryMeanFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : ℝ :=
  ∑ j, e.batteryEnergy j * (batteryFinal e t j j).re

def batteryEnergyChange {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : ℝ :=
  batteryMeanFinal e t - e.batteryEnergy e.initialLevel

def batteryAbsoluteTail {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : ℝ :=
  ∑ j, |e.batteryEnergy j - e.batteryEnergy e.nominalLevel| * (batteryFinal e t j j).re

def controllerProductDefect {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : ℝ :=
  let reshaped : Mat (Fin e.c × ((Fin e.w × Fin e.r) × (Payload I × Fin r))) :=
    (finalState e.extension t).submatrix
      (fun x => (e.split.symm (x.1, x.2.1), x.2.2))
      (fun x => (e.split.symm (x.1, x.2.1), x.2.2))
  traceDistance reshaped (e.controller.matrix ⊗ₖ partialLeft reshaped)

structure Budget where
  productError : ℝ
  controllerEnergy : ℝ
  controllerEntropy : ℝ
  batteryEntropy : ℝ
  failureProbability : ℝ
  absoluteTail : ℝ

def MeetsBudget {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (b : Budget) : Prop :=
  (0 ≤ b.productError ∧ 0 ≤ b.controllerEnergy ∧ 0 ≤ b.controllerEntropy ∧
   0 ≤ b.batteryEntropy ∧ 0 ≤ b.failureProbability ∧ 0 ≤ b.absoluteTail) ∧
  ∀ r (t : Tester S r),
    controllerProductDefect e t ≤ b.productError ∧
    |controllerEnergyChange e t| ≤ b.controllerEnergy ∧
    |controllerEntropyChange e t| ≤ b.controllerEntropy ∧
    entropy (batteryFinal e t) ≤ b.batteryEntropy ∧
    1 - (batteryFinal e t e.nominalLevel e.nominalLevel).re ≤ b.failureProbability ∧
    batteryAbsoluteTail e t ≤ b.absoluteTail

def BudgetFamilyReturns (b : ℕ → Budget) : Prop :=
  Vanishes (fun n => (b n).productError) ∧
  Sublinear (fun n => (b n).controllerEnergy) ∧
  Sublinear (fun n => (b n).controllerEntropy) ∧
  Sublinear (fun n => (b n).batteryEntropy) ∧
  Vanishes (fun n => (b n).failureProbability) ∧
  Sublinear (fun n => (b n).absoluteTail)

structure Implementation (β : ℝ) (T : TaskFamily) where
  engine : (n : ℕ) → Engine (T.schedule n) β
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  error_vanishes : Vanishes error
  service : ∀ n, Approximates (engine n).extension (T.target n) (error n)
  budget : ℕ → Budget
  endpoints : ∀ n, MeetsBudget (engine n) (budget n)
  returns : BudgetFamilyReturns budget

def implementationRate {β : ℝ} {T : TaskFamily} (d : Implementation β T) : EReal :=
  limsup (fun n => ((nominalDebit (d.engine n) / (n + 1 : ℝ) : ℝ) : EReal)) atTop

def optimalWork (β : ℝ) (T : TaskFamily) : EReal :=
  ⨅ d : Implementation β T, implementationRate d

/-- The requested lower bound, equality, and actual attainment, with all block
families and all compatible testers quantified through the definitions above. -/
def WorkLaw (β : ℝ) (T : TaskFamily) : Prop :=
  (∀ d : Implementation β T, regularizedCost β T ≤ implementationRate d) ∧
  optimalWork β T = regularizedCost β T ∧
  (∃ d : Implementation β T, implementationRate d = regularizedCost β T)

/-- Main-text bits convention, separate from the nats convention of WorkLaw. -/
def WorkLawBits (β : ℝ) (T : TaskFamily) : Prop :=
  optimalWork β T = ((Real.log 2 / β : ℝ) : EReal) * Kbeta β T

/-- Numerical ledger quantities. The following structure does not claim these
identities or positivity properties have been derived from the engine circuit. -/
structure Ledger where
  controllerEnergy : ℝ
  batteryEnergy : ℝ
  reservoirEnergy : ℝ
  handoffEnergy : ℝ
  controllerEntropy : ℝ
  batteryEntropy : ℝ
  reservoirEntropy : ℝ
  deviceEntropy : ℝ
  relativeEntropy : ℝ
  totalCorrelation : ℝ

def Ledger.Accounts (l : Ledger) (β : ℝ) : Prop :=
  l.deviceEntropy = l.controllerEntropy + l.batteryEntropy + l.reservoirEntropy - l.totalCorrelation ∧
  l.reservoirEntropy = β * l.reservoirEnergy - l.relativeEntropy ∧
  l.controllerEnergy + l.batteryEnergy + l.reservoirEnergy + l.handoffEnergy = 0

def Ledger.Score (l : Ledger) (β : ℝ) : ℝ := l.handoffEnergy + l.deviceEntropy / β

def LedgerBound (l : Ledger) (β : ℝ) (d u s b v : ℝ) : Prop :=
  l.Score β - u - v - (s + b) / β ≤ d

def engineLedger {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) : Ledger where
  controllerEnergy := controllerEnergyChange e t
  batteryEnergy := batteryEnergyChange e t
  reservoirEnergy := energy e.HR.matrix (reservoirFinal e t) - energy e.HR.matrix (gibbs β e.HR)
  handoffEnergy := handoff e.extension t
  controllerEntropy := controllerEntropyChange e t
  batteryEntropy := entropy (batteryFinal e t)
  reservoirEntropy := entropy (reservoirFinal e t) - entropy (gibbs β e.HR)
  deviceEntropy := entropy (bodyOutput e.extension t) - entropy e.extension.source.matrix
  relativeEntropy := faithfulRelativeEntropy (reservoirFinal e t) (gibbs β e.HR)
  totalCorrelation := entropy (controllerFinal e t) + entropy (batteryFinal e t) +
    entropy (reservoirFinal e t) - entropy (bodyOutput e.extension t)

/-- The finite accounting proof package. PhysicalConverse derives all five
fields from Engine, circuit density invariants, source entropy additivity,
the Gibbs heat identity, schedule conservation, and checked entropy inequalities.
No field is an external hypothesis of the unconditional physical bound.
The separate *_of_accounting lemmas retain this package as a reusable explicit
argument. Sources: Reeb--Wolf (2014) for finite-reservoir accounting and the
attributed QuantumInfo entropy proofs vendored at the exact Mathlib pin.
-/
structure PhysicalAccountingData {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) : Prop where
  accounts : ∀ r (t : Tester S r), (engineLedger e t).Accounts β
  relative_nonneg : ∀ r (t : Tester S r), 0 ≤ (engineLedger e t).relativeEntropy
  correlation_nonneg : ∀ r (t : Tester S r), 0 ≤ (engineLedger e t).totalCorrelation
  battery_nonneg : ∀ r (t : Tester S r) j, 0 ≤ (batteryFinal e t j j).re
  battery_normalized : ∀ r (t : Tester S r), ∑ j, (batteryFinal e t j j).re = 1

end ScheduleLaw
