import PhaseVectorDistance

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseHistoryTelescope
open PhaseVectorDistance
variable {a : Type} [Fintype a] [DecidableEq a]

def run (U : ℕ → Mat a) (ψ : a → ℂ) : ℕ → a → ℂ
  | 0 => ψ
  | n+1 => U n *ᵥ run U ψ n

theorem run_norm (U : ℕ → Mat a) (hU : ∀ n,IsUnitary (U n)) (ψ : a → ℂ) (n : ℕ) :
    ‖vector (run U ψ n)‖=‖vector ψ‖ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run,norm_unitary _ (hU n),ih]

/-- Every one-step estimate is applied only to the ideal old history.
No actual intermediate phase factorization is assumed. -/
theorem telescope (U V : ℕ → Mat a) (hU : ∀ n,IsUnitary (U n)) (ψ : a → ℂ)
    (ε : ℕ → ℝ) (hε : ∀ n,‖vector ((U n-V n) *ᵥ run V ψ n)‖≤ε n) (n : ℕ) :
    ‖vector (run U ψ n)-vector (run V ψ n)‖≤∑ k∈Finset.range n,ε k := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hh : vector (run U ψ (n+1))-vector (run V ψ (n+1))=
        vector (U n *ᵥ (run U ψ n-run V ψ n))+vector ((U n-V n) *ᵥ run V ψ n) := by
      apply WithLp.ofLp_injective 2
      funext i
      simp only [run,vector,PiLp.toLp_apply,PiLp.sub_apply,PiLp.add_apply,
        Matrix.mulVec,dotProduct,Pi.sub_apply,Matrix.sub_apply,sub_mul,mul_sub,
        Finset.sum_sub_distrib]
      ring
    rw [hh,Finset.sum_range_succ]
    calc _ ≤ ‖vector (U n *ᵥ (run U ψ n-run V ψ n))‖+
        ‖vector ((U n-V n) *ᵥ run V ψ n)‖ := norm_add_le _ _
         _ ≤ (∑ k∈Finset.range n,ε k)+ε n := by
           rw [norm_unitary _ (hU n)]
           exact add_le_add ih (hε n)

theorem pure_history (U V : ℕ → Mat a) (hU : ∀ n,IsUnitary (U n)) (hV : ∀ n,IsUnitary (V n))
    (ψ : a → ℂ) (hψ : ‖vector ψ‖=1) (ε : ℕ → ℝ)
    (hε : ∀ n,‖vector ((U n-V n) *ᵥ run V ψ n)‖≤ε n) (n : ℕ) :
    traceDistance (pureMatrix (run U ψ n)) (pureMatrix (run V ψ n))≤∑ k∈Finset.range n,ε k :=
  (pure_distance _ _ ((run_norm U hU ψ n).trans hψ) ((run_norm V hV ψ n).trans hψ)).trans
    (telescope U V hU ψ ε hε n)

end ScheduleLaw.Blueprint.PhaseHistoryTelescope
