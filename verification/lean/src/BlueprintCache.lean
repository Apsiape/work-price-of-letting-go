import CacheProtocol
import BlueprintFactory
import W2.TensorFamily
import BlueprintHeatEffect

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Whole-rest return includes retired thermal stocks and factory residues;
the initialized energy defect includes all of them, not a selected branch. -/
theorem cyclic_cache_protocol {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g η : ℝ) (hη : 0 < η) (P : InitializedPlan β e g η)
    (hf : FactoryFamily β P.bare.source P.reference) :
    ∃ (p : Driven S β) (b : Budget), Driven.CapitalCharged p ∧
      Approximates p.extension P.bare η ∧ Driven.Meets p b ∧ SmallBudget b η ∧
      (∀ r (t : Tester S r), |Driven.defect p t| ≤ P.residual+η) ∧
      Driven.nominalDebit p ≤ sourceFreeTerm β P.bare P.reference+P.w+η := by
  exact CacheProtocol.realizes β hβ e g η hη P

end ScheduleLaw.Blueprint
