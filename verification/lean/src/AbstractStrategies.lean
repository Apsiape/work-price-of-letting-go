import Foundations

/-! A precise boundary for the optional finite causal Stinespring hypothesis.
Memory dimensions may change after every cut. Each contact is a finite Kraus
channel on the memory and the currently held physical carriers. All discarded
systems are represented by its Kraus index. No entropy or work claim is part
of the completeness hypothesis below. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace ScheduleLaw

structure FiniteKrausChannel (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] where
  count : ℕ
  kraus : Fin count → Matrix b a ℂ
  normalized : ∑ j, (kraus j)ᴴ * kraus j = 1

structure AbstractFiniteStrategy {I : Inventory} (S : Schedule I) where
  memory : ℕ → ℕ
  memory_pos : ∀ n, n ≤ 2 * S.visits + 1 → 0 < memory n
  source : Density (Fin (memory 0))
  contact : (k : Cut S) → FiniteKrausChannel
    (Fin (memory k.val) × Restricted I (held S k))
    (Fin (memory (k.val+1)) × Restricted I (held S k))

def AbstractFiniteStrategy.liftedKraus {I : Inventory} {S : Schedule I}
    (a : AbstractFiniteStrategy S) (k : Cut S) (j : Fin (a.contact k).count) (r : ℕ) :
    Matrix (Fin (a.memory (k.val+1)) × (Payload I × Fin r))
      (Fin (a.memory k.val) × (Payload I × Fin r)) ℂ :=
  fun x y => (a.contact k).kraus j
    (x.1, restrictPayload I (held S k) x.2.1)
    (y.1, restrictPayload I (held S k) y.2.1) *
      if x.2.2 = y.2.2 ∧
        restrictPayload I (held S k)ᶜ x.2.1 = restrictPayload I (held S k)ᶜ y.2.1
      then 1 else 0

def AbstractFiniteStrategy.testerGate {I : Inventory} {S : Schedule I}
    (a : AbstractFiniteStrategy S) {r : ℕ} (t : Tester S r) (k : Cut S) :
    Mat (Fin (a.memory (k.val+1)) × (Payload I × Fin r)) :=
  fun x y => (if x.1 = y.1 then 1 else 0) *
    t.gate k (x.2.2,x.2.1) (y.2.2,y.2.1)

def AbstractFiniteStrategy.run {I : Inventory} {S : Schedule I}
    (a : AbstractFiniteStrategy S) {r : ℕ} (t : Tester S r) :
    (n : ℕ) → Mat (Fin (a.memory n) × (Payload I × Fin r))
  | 0 => a.source.matrix ⊗ₖ pureMatrix (fun x : Payload I × Fin r => t.initial (x.2,x.1))
  | n+1 => if h : n < 2 * S.visits + 1 then
      evolve (a.testerGate t ⟨n,h⟩)
        (∑ j, a.liftedKraus ⟨n,h⟩ j r * a.run t n * (a.liftedKraus ⟨n,h⟩ j r)ᴴ)
    else 0

def AbstractFiniteStrategy.observerOutput {I : Inventory} {S : Schedule I}
    (a : AbstractFiniteStrategy S) {r : ℕ} (t : Tester S r) : Mat (Payload I × Fin r) :=
  partialLeft (a.run t (2 * S.visits + 1))

/-- Precisely scoped optional hypothesis: every finite causal Kraus strategy
has one finite unitary dilation with an independent purified source and the
same output against every coherent tester, uniformly in tester memory. The
dilation may retain all discarded systems. This proposition is not postulated
as an axiom and is not used by the modelled-circuit converse. -/
def FiniteCausalStinespringCompleteness : Prop :=
  ∀ (I : Inventory) (S : Schedule I) (a : AbstractFiniteStrategy S),
    ∃ e : Extension S, ∀ r (t : Tester S r),
      observerOutput e t = a.observerOutput t

structure AbstractTaskFamily where
  inventory : ℕ → Inventory
  schedule : (n : ℕ) → Schedule (inventory n)
  strategy : (n : ℕ) → AbstractFiniteStrategy (schedule n)

def AbstractTaskFamily.realize (hcausal : FiniteCausalStinespringCompleteness)
    (T : AbstractTaskFamily) : TaskFamily where
  inventory := T.inventory
  schedule := T.schedule
  target n := Classical.choose (hcausal (T.inventory n) (T.schedule n) (T.strategy n))

theorem AbstractTaskFamily.realize_output (hcausal : FiniteCausalStinespringCompleteness)
    (T : AbstractTaskFamily) (n r : ℕ) (t : Tester (T.schedule n) r) :
    observerOutput ((T.realize hcausal).target n) t = (T.strategy n).observerOutput t :=
  Classical.choose_spec (hcausal (T.inventory n) (T.schedule n) (T.strategy n)) r t

def abstractFiniteCost {I : Inventory} {S : Schedule I}
    (β : ℝ) (a : AbstractFiniteStrategy S) (ε : ℝ) : EReal :=
  ⨅ (e : Extension S)
    (_ : ∀ r (t : Tester S r),traceDistance (observerOutput e t) (a.observerOutput t) ≤ ε),
    ⨆ r,⨆ t : Tester S r,(score β e t : EReal)

def abstractRegularizedCost (β : ℝ) (T : AbstractTaskFamily) : EReal :=
  ⨅ (ε : ℕ → ℝ) (_ : (∀ n,0 ≤ ε n) ∧ Vanishes ε),
    Filter.limsup (fun n => abstractFiniteCost β (T.strategy n) (ε n) /
      ((n+1 : ℝ) : EReal)) Filter.atTop

theorem abstract_finiteCost_realization (hcausal : FiniteCausalStinespringCompleteness)
    (β : ℝ) (T : AbstractTaskFamily) (n : ℕ) (ε : ℝ) :
    finiteCost β ((T.realize hcausal).target n) ε = abstractFiniteCost β (T.strategy n) ε := by
  simp only [finiteCost,abstractFiniteCost,Approximates,T.realize_output hcausal]
  rfl

theorem abstract_regularizedCost_realization (hcausal : FiniteCausalStinespringCompleteness)
    (β : ℝ) (T : AbstractTaskFamily) :
    regularizedCost β (T.realize hcausal) = abstractRegularizedCost β T := by
  simp only [regularizedCost,abstractRegularizedCost,abstract_finiteCost_realization hcausal]

end ScheduleLaw
