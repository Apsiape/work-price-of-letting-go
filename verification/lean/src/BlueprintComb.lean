import BlueprintContracts
import BlueprintUnitaryCompletion
import BlueprintPrefixInduction

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Actual fixed-memory Recorder realization of every causal prefix family,
including both zero visits and the schedule-wide positive-visit induction. -/
theorem lawful_tester_from_prefixes {I : Inventory} (S : Schedule I)
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) :
    ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t = Z b := by
  by_cases hz : S.visits=0
  · exact zero_visit_comb_realization S hz Z
  · exact positive_visit_comb_realization S (Nat.pos_of_ne_zero hz) Z hZ

theorem eliminate_comb : CombRealization := by
  intro I S Z hZ
  exact lawful_tester_from_prefixes S Z hZ

end ScheduleLaw.Blueprint
