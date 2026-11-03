import WireEvolution
import CircuitProbe
import ActualSlackBounds
import PhysicalConverse
import Factory
import Lift

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Local response matrices; no tester dimension occurs in this type. -/
def CutKernel {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S) :=
  Matrix (Fin e.b × Restricted I (held S k))
    (Recorder.Stock S × Restricted I (held S k)) ℂ

def kernelLift {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (r : ℕ) (K : CutKernel e k) : Matrix (Global e r) (Raw S r) ℂ := fun i j =>
  K (i.1,restrictPayload I (held S k) i.2.1) (j.1,restrictPayload I (held S k) j.2.1) *
    if restrictPayload I (held S k)ᶜ i.2.1 = restrictPayload I (held S k)ᶜ j.2.1 ∧
      i.2.2 = j.2.2 then 1 else 0

def sourceBlock {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (f g : Fin e.f) : Mat (Global e r) :=
  (pureMatrix (purifiedVector e t n)).submatrix (fun i => (i,f)) (fun j => (j,g))

def terminalStock {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) :
    Mat (Recorder.Stock S) := partialRight (rawState t (2*S.visits+1))

def OperationalImage {I : Inventory} {S : Schedule I} (e : Extension S) :
    Set (Mat (Fin e.b) × ℝ) := {x | ∃ (r : ℕ) (t : Tester S r),
      x = (bodyOutput e t,handoff e t)}

def SectionDensities (d : ℕ) (K : Set (Mat (Fin d) × ℝ)) : Prop :=
  ∀ x ∈ K, x.1.PosSemidef ∧ x.1.trace = 1

def KernelContained {d : ℕ} (ρ ζ : Mat (Fin d)) : Prop :=
  ∀ v : Fin d → ℂ, ζ *ᵥ v = 0 → ρ *ᵥ v = 0

def whiteNoise {d : ℕ} (ζ : Mat (Fin d)) (s : ℝ) : Mat (Fin d) :=
  (((1-s : ℝ) : ℂ) • ζ) + (((s/(d : ℝ) : ℝ) : ℂ) • 1)

def TangentConclusion {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    (g s : ℝ) : Prop :=
  ∃ q : Density (Fin e.b), q.matrix.PosDef ∧ ∃ w : ℝ,
    (∀ r (t : Tester S r), physicalLinearized β e q t ≤ w) ∧
    (∃ (r : ℕ) (t : Tester S r), physicalLinearized β e q t = w) ∧
    sourceFreeTerm β e q + w ≤ g - Real.log (1-s)/β

def SmallBudget (b : Budget) (η : ℝ) : Prop :=
  b.productError ≤ η ∧ b.controllerEnergy ≤ η ∧ b.controllerEntropy ≤ η ∧
  b.batteryEntropy ≤ η ∧ b.failureProbability ≤ η ∧ b.absoluteTail ≤ η

def CompilerConclusion {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    (g ν : ℝ) : Prop := ∃ (d : Engine S β) (b : Budget),
  Approximates d.extension e ν ∧ MeetsBudget d b ∧ SmallBudget b ν ∧ nominalDebit d ≤ g+ν

/-- Bare circuit with the terminal heat correction already inserted. All
energy statements use its actual source and actual body/handoff outputs. -/
structure InitializedPlan {I : Inventory} {S : Schedule I} (β : ℝ)
    (e : Extension S) (g η : ℝ) where
  bare : Extension S
  reference : Density (Fin bare.b)
  faithful : reference.matrix.PosDef
  w : ℝ
  residual : ℝ
  residual_nonneg : 0 ≤ residual
  residual_small : residual ≤ η
  service : Approximates bare e η
  rate : sourceFreeTerm β bare reference + w ≤ g+η
  initialized : ∀ r (t : Tester S r), |physicalLinearized β bare reference t-w| ≤ residual

/-- The physical hardware before its nonconserving gates are phase-lifted.
No conservation proof is included or assumed by this data structure. -/
structure Driven {I : Inventory} (S : Schedule I) (β : ℝ) where
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
  capital : ℝ
  source_product : extension.source.matrix =
    (controller.matrix ⊗ₖ (pureMatrix (fun j => if j = initialLevel then 1 else 0) ⊗ₖ
      gibbs β HR)).submatrix split split

namespace Driven
def nominalDebit {I : Inventory} {S : Schedule I} {β : ℝ} (e : Driven S β) : ℝ :=
  e.batteryEnergy e.initialLevel - e.batteryEnergy e.nominalLevel

def controllerFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : Mat (Fin e.c) :=
  partialRight ((bodyOutput e.extension t).submatrix e.split.symm e.split.symm)

def batteryReservoirFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : Mat (Fin e.w × Fin e.r) :=
  partialLeft ((bodyOutput e.extension t).submatrix e.split.symm e.split.symm)

def batteryFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) :=
  partialRight (batteryReservoirFinal e t)

def reservoirFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) :=
  partialLeft (batteryReservoirFinal e t)

def controllerEnergyChange {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : ℝ :=
  energy e.HC.matrix (controllerFinal e t) - energy e.HC.matrix e.controller.matrix

def controllerEntropyChange {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : ℝ :=
  entropy (controllerFinal e t) - entropy e.controller.matrix

def batteryMeanFinal {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : ℝ :=
  ∑ j, e.batteryEnergy j * (batteryFinal e t j j).re

def batteryEnergyChange {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : ℝ :=
  batteryMeanFinal e t - e.batteryEnergy e.initialLevel

def batteryAbsoluteTail {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : ℝ :=
  ∑ j, |e.batteryEnergy j - e.batteryEnergy e.nominalLevel| * (batteryFinal e t j j).re

def controllerProductDefect {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Driven S β) {r : ℕ} (t : Tester S r) : ℝ :=
  let reshaped : Mat (Fin e.c × ((Fin e.w × Fin e.r) × (Payload I × Fin r))) :=
    (finalState e.extension t).submatrix
      (fun x => (e.split.symm (x.1, x.2.1), x.2.2))
      (fun x => (e.split.symm (x.1, x.2.1), x.2.2))
  traceDistance reshaped (e.controller.matrix ⊗ₖ partialLeft reshaped)


def bodyHamiltonian {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β) :
    Mat (Fin p.extension.b) :=
  (p.HC.matrix ⊗ₖ (1 : Mat (Fin p.w × Fin p.r)) + (1 : Mat (Fin p.c)) ⊗ₖ
    ((diagonal fun j => (p.batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin p.r)) +
      (1 : Mat (Fin p.w)) ⊗ₖ p.HR.matrix)).submatrix p.split p.split

def defect {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β)
    {r : ℕ} (t : Tester S r) : ℝ := handoff p.extension t +
  energy p.bodyHamiltonian (bodyOutput p.extension t-p.extension.source.matrix)

def Meets {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β) (b : Budget) : Prop :=
  (0 ≤ b.productError ∧ 0 ≤ b.controllerEnergy ∧ 0 ≤ b.controllerEntropy ∧
   0 ≤ b.batteryEntropy ∧ 0 ≤ b.failureProbability ∧ 0 ≤ b.absoluteTail) ∧
  ∀ r (t : Tester S r), controllerProductDefect p t ≤ b.productError ∧
    |controllerEnergyChange p t| ≤ b.controllerEnergy ∧
    |controllerEntropyChange p t| ≤ b.controllerEntropy ∧
    entropy (batteryFinal p t) ≤ b.batteryEntropy ∧
    1-(batteryFinal p t p.nominalLevel p.nominalLevel).re ≤ b.failureProbability ∧
    batteryAbsoluteTail p t ≤ b.absoluteTail

def CapitalCharged {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β) : Prop :=
  faithfulRelativeEntropy p.controller.matrix (gibbs β p.HC)/β ≤ p.capital
end Driven

/-- m independent copies, including all off-diagonal entries. -/
def tensorPower {d : ℕ} (A : Mat (Fin d)) (m : ℕ) : Mat (Fin m → Fin d) :=
  fun i j => ∏ k, A (i k) (j k)

def tensorHamiltonian {d : ℕ} (H : Mat (Fin d)) (m : ℕ) : Mat (Fin m → Fin d) :=
  fun i j => ∑ k, H (i k) (j k) * if ∀ l, l ≠ k → i l = j l then 1 else 0

/-- Formation circuit before the common conserving phase lift. The formed batch remains part of
its physical Gibbs reservoir; all coding residues remain physical too. -/
structure Formation {d : ℕ} (β : ℝ) (τ q : Density (Fin d)) (m : ℕ) where
  inventory : Inventory
  schedule : Schedule inventory
  empty : schedule.visits = 0
  hardware : Driven schedule β
  aux : ℕ
  aux_pos : 0 < aux
  reservoirSplit : Fin hardware.r ≃ (Fin m → Fin d) × Fin aux
  auxiliaryHamiltonian : Hamiltonian (Fin aux)
  reservoirHamiltonian : hardware.HR.matrix.submatrix reservoirSplit.symm reservoirSplit.symm =
    tensorHamiltonian (tangentHamiltonian β q) m ⊗ₖ (1 : Mat (Fin aux)) +
      (1 : Mat (Fin m → Fin d)) ⊗ₖ auxiliaryHamiltonian.matrix
  initial_batch : partialRight ((gibbs β hardware.HR).submatrix
    reservoirSplit.symm reservoirSplit.symm) = tensorPower q.matrix m
  debit : ℝ
  debit_eq : Driven.nominalDebit hardware = (m : ℝ)*debit

namespace Formation

def output {d : ℕ} {β : ℝ} {τ q : Density (Fin d)} {m : ℕ}
    (f : Formation β τ q m) : Mat (Fin m → Fin d) :=
  partialRight ((Driven.reservoirFinal f.hardware (idleTester f.schedule)).submatrix
    f.reservoirSplit.symm f.reservoirSplit.symm)
end Formation

/-- Factory accuracy/rate plus tunably small helper tail and controller
returns, for every sufficiently large m. The batch output is not required
independent of the discarded coding and thermal residues. -/
def FactoryFamily {d : ℕ} (β : ℝ) (τ q : Density (Fin d)) : Prop :=
  ∃ (a err : ℕ → ℝ) (A : ℝ), 0 ≤ A ∧
    Tendsto a atTop (𝓝 (faithfulRelativeEntropy τ.matrix q.matrix/β)) ∧
    Vanishes err ∧ (∀ m, 0 ≤ err m) ∧
    ∀ᶠ m : ℕ in atTop, ∀ η f : ℝ, 0 < η → 0 < f →
      ∃ (F : Formation β τ q m) (b : Budget), F.debit = a m ∧
        traceDistance F.output (tensorPower τ.matrix m) ≤ err m ∧ Driven.Meets F.hardware b ∧
        b.productError ≤ η ∧ b.controllerEnergy ≤ η ∧ b.controllerEntropy ≤ η ∧
        b.batteryEntropy ≤ η ∧ b.failureProbability ≤ f ∧ b.absoluteTail ≤ (m : ℝ)*A*f ∧
        (∀ r (t : Tester F.schedule r), |Driven.defect F.hardware t| ≤ (m : ℝ)*A*(err m+f)) ∧
        Driven.CapitalCharged F.hardware

end ScheduleLaw.Blueprint
