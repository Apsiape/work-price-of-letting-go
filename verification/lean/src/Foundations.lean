import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
Concrete finite matrix definitions for the schedule-law challenge.
Entropy is in nats. The zero value on non-Hermitian matrices is only a totalization;
no physical claim is made for such matrices. No analytic or thermodynamic fact is
assumed by these definitions.
-/

set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker Topology ComplexOrder
namespace ScheduleLaw

abbrev Mat (n : Type) := Matrix n n ℂ

structure Density (n : Type) [Fintype n] where
  matrix : Mat n
  positive : matrix.PosSemidef
  normalized : matrix.trace = 1

def entropy {n : Type} [Fintype n] [DecidableEq n] (ρ : Mat n) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

def matrixLog {n : Type} [Fintype n] [DecidableEq n] (ρ : Mat n) : Mat n :=
  if h : ρ.IsHermitian then h.cfc Real.log else 0

/-- Only used with a faithful right argument. The singular-support extension is
deliberately not asserted to be the general extended-real relative entropy. -/
def faithfulRelativeEntropy {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Mat n) : ℝ := -entropy ρ - (ρ * matrixLog σ).trace.re

structure Hamiltonian (n : Type) [Fintype n] where
  matrix : Mat n
  hermitian : matrix.IsHermitian

def energy {n : Type} [Fintype n] (H ρ : Mat n) : ℝ := (H * ρ).trace.re

def gibbs {n : Type} [Fintype n] [DecidableEq n]
    (β : ℝ) (H : Hamiltonian n) : Mat n :=
  let Z := ∑ i, Real.exp (-β * H.hermitian.eigenvalues i)
  H.hermitian.cfc (fun x => Real.exp (-β * x) / Z)

def IsUnitary {n : Type} [Fintype n] [DecidableEq n] (U : Mat n) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

def Conserves {n : Type} [Fintype n] (U H : Mat n) : Prop := Uᴴ * H * U = H

def evolve {n : Type} [Fintype n] (U ρ : Mat n) : Mat n := U * ρ * Uᴴ

def pureMatrix {n : Type} (v : n → ℂ) : Mat n := fun i j => v i * star (v j)

def partialRight {a b : Type} [Fintype b] (ρ : Mat (a × b)) : Mat a :=
  fun i j => ∑ k, ρ (i, k) (j, k)

def partialLeft {a b : Type} [Fintype a] (ρ : Mat (a × b)) : Mat b :=
  fun i j => ∑ k, ρ (k, i) (k, j)

def traceNorm {n : Type} [Fintype n] [DecidableEq n] (A : Mat n) : ℝ :=
  ∑ i, Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

def traceDistance {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Mat n) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- Physical carrier identities, each with one fixed Hilbert space and Hamiltonian. -/
structure Inventory where
  count : ℕ
  dim : Fin count → ℕ
  dim_pos : ∀ c, 0 < dim c
  H : (c : Fin count) → Hamiltonian (Fin (dim c))

abbrev Payload (I : Inventory) := (c : Fin I.count) → Fin (I.dim c)

/-- Every event is one endpoint of one visit. `false` = arrival, `true` = release.
The endpoint equivalence resolves all ties. Distinct visits of one carrier cannot overlap. -/
structure Schedule (I : Inventory) where
  visits : ℕ
  carrier : Fin visits → Fin I.count
  position : (Fin visits × Bool) ≃ Fin (2 * visits)
  ordered : ∀ v, position (v, false) < position (v, true)
  disjoint : ∀ v w, v ≠ w → carrier v = carrier w →
    position (v, true) < position (w, false) ∨ position (w, true) < position (v, false)

abbrev Cut {I : Inventory} (S : Schedule I) := Fin (2 * S.visits + 1)

def held {I : Inventory} (S : Schedule I) (k : Cut S) : Finset (Fin I.count) :=
  Finset.univ.filter fun c => ∃ v, S.carrier v = c ∧
    (S.position (v, false)).val < k.val ∧ k.val ≤ (S.position (v, true)).val

abbrev Restricted (I : Inventory) (A : Finset (Fin I.count)) :=
  (c : {c // c ∈ A}) → Fin (I.dim c.val)

def restrictPayload (I : Inventory) (A : Finset (Fin I.count)) (p : Payload I) :
    Restricted I A := fun c => p c.val

/-- An exact square unitary on the body and the listed carriers, tensored with
identity on all other physical carriers. This is a matrix locality condition,
not a predicate supplied by the user. -/
def LocalOn (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Fin b × Payload I)) : Prop :=
  ∃ V : Mat (Fin b × Restricted I A), IsUnitary V ∧
    ∀ i j, U i j = V (i.1, restrictPayload I A i.2) (j.1, restrictPayload I A j.2) *
      if restrictPayload I Aᶜ i.2 = restrictPayload I Aᶜ j.2 then 1 else 0

def payloadHamiltonian (I : Inventory) : Mat (Payload I) :=
  fun p q => ∑ c, (I.H c).matrix (p c) (q c) *
    if ∀ d, d ≠ c → p d = q d then 1 else 0

/-- The purification is part of the data and is never passed to a gate. -/
structure Extension {I : Inventory} (S : Schedule I) where
  b : ℕ
  b_pos : 0 < b
  source : Density (Fin b)
  f : ℕ
  f_pos : 0 < f
  purification : Fin b × Fin f → ℂ
  purification_norm : ∑ i, Complex.normSq (purification i) = 1
  purification_reduces : partialRight (pureMatrix purification) = source.matrix
  gate : Cut S → Mat (Fin b × Payload I)
  unitary : ∀ k, IsUnitary (gate k)
  gate_local : ∀ k, LocalOn I b (held S k) (gate k)

/-- A coherent adaptive observer. Its initial pure state includes all future
inputs and references. All its gates act on its memory and unheld carriers.
The memory dimension is universally quantified in service claims. -/
structure Tester {I : Inventory} (S : Schedule I) (r : ℕ) where
  initial : Fin r × Payload I → ℂ
  normalized : ∑ i, Complex.normSq (initial i) = 1
  gate : Cut S → Mat (Fin r × Payload I)
  unitary : ∀ k, IsUnitary (gate k)
  gate_local : ∀ k, LocalOn I r (held S k)ᶜ (gate k)

abbrev Global {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ) :=
  Fin e.b × (Payload I × Fin r)

def initialState {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : Mat (Global e r) :=
  e.source.matrix ⊗ₖ pureMatrix (fun x : Payload I × Fin r => t.initial (x.2, x.1))

def jointGate {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) : Mat (Global e r) :=
  let Ud : Mat (Global e r) := fun i j =>
    e.gate k (i.1, i.2.1) (j.1, j.2.1) * if i.2.2 = j.2.2 then 1 else 0
  let Ut : Mat (Global e r) := fun i j =>
    (if i.1 = j.1 then 1 else 0) * t.gate k (i.2.2, i.2.1) (j.2.2, j.2.1)
  Ut * Ud

/-- State immediately before the next event after the indicated number of cuts.
The ownership event itself only changes which gates may touch the carrier. -/
def run {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : ℕ → Mat (Global e r)
  | 0 => initialState e t
  | n + 1 => if h : n < 2 * S.visits + 1 then
      evolve (jointGate e t ⟨n, h⟩) (run e t n) else run e t n

def finalState {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) := run e t (2 * S.visits + 1)

def observerOutput {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) := partialLeft (finalState e t)

def bodyOutput {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) := partialRight (finalState e t)

def carrierEnergy {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (ρ : Mat (Global e r)) (c : Fin I.count) : ℝ :=
  energy (fun i j => (if i.1 = j.1 ∧ i.2.2 = j.2.2 ∧
    (∀ d, d ≠ c → i.2.1 d = j.2.1 d) then 1 else 0) *
    (I.H c).matrix (i.2.1 c) (j.2.1 c)) ρ

def handoff {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : ℝ :=
  ∑ v, (carrierEnergy e (run e t ((S.position (v, true)).val + 1)) (S.carrier v) -
    carrierEnergy e (run e t ((S.position (v, false)).val + 1)) (S.carrier v))

def score {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    {r : ℕ} (t : Tester S r) : ℝ :=
  (entropy (bodyOutput e t) - entropy e.source.matrix) / β + handoff e t

/-- Targets are finite unitary dilations. Equivalence to all finite strategies
requires the usual finite causal dilation theorem; it is not proved here. -/
abbrev Target {I : Inventory} (S : Schedule I) := Extension S

def Approximates {I : Inventory} {S : Schedule I}
    (e T : Extension S) (ε : ℝ) : Prop :=
  ∀ r (t : Tester S r), traceDistance (observerOutput e t) (observerOutput T t) ≤ ε

def finiteCost {I : Inventory} {S : Schedule I} (β : ℝ) (T : Target S) (ε : ℝ) : EReal :=
  ⨅ (e : Extension S) (_ : Approximates e T ε), ⨆ r, ⨆ t : Tester S r, (score β e t : EReal)

def Vanishes (a : ℕ → ℝ) : Prop := Tendsto a atTop (𝓝 0)

def Sublinear (a : ℕ → ℝ) : Prop := Vanishes (fun n => a n / (n + 1 : ℝ))

/-- Index n represents a block of n+1 uses, avoiding an irrelevant zero-use denominator. -/
structure TaskFamily where
  inventory : ℕ → Inventory
  schedule : (n : ℕ) → Schedule (inventory n)
  target : (n : ℕ) → Target (schedule n)

def regularizedCost (β : ℝ) (T : TaskFamily) : EReal :=
  ⨅ (ε : ℕ → ℝ) (_ : (∀ n, 0 ≤ ε n) ∧ Vanishes ε),
    limsup (fun n => finiteCost β (T.target n) (ε n) / ((n + 1 : ℝ) : EReal)) atTop

def Kbeta (β : ℝ) (T : TaskFamily) : EReal :=
  ((β / Real.log 2 : ℝ) : EReal) * regularizedCost β T

end ScheduleLaw
