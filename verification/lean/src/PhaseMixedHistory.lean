import PhaseHistoryTelescope
import FactoryOutput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseMixedHistory
variable {a : Type} [Fintype a] [DecidableEq a]

def run (U : ℕ → Mat a) (ρ : Mat a) : ℕ → Mat a
  | 0 => ρ
  | n+1 => evolve (U n) (run U ρ n)

/-- Local channel accuracy is tested only on the ideal evolving state.
The actual state may be correlated with the phase after every cut. -/
theorem telescope (U V : ℕ → Mat a) (hU : ∀ n,IsUnitary (U n)) (ρ : Mat a)
    (ε : ℕ → ℝ)
    (hε : ∀ n,traceDistance (evolve (U n) (run V ρ n)) (evolve (V n) (run V ρ n))≤ε n)
    (n : ℕ) : traceDistance (run U ρ n) (run V ρ n)≤∑ k∈Finset.range n,ε k := by
  induction n with
  | zero => simp [run,W2.traceDistance_self]
  | succ n ih =>
    rw [run,run,Finset.sum_range_succ]
    exact (FactoryOutput.distance_triangle _ (evolve (U n) (run V ρ n)) _).trans (by
      rw [FiniteResidue.traceDistance_unitary _ _ _ (hU n)]
      exact add_le_add ih (hε n))

end ScheduleLaw.Blueprint.PhaseMixedHistory
