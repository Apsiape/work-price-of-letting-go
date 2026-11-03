import BlueprintFinitePrimitives
import PhaseProtocol

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Finite whole-history phase compilation. All gates of the resulting
Engine conserve its one fixed Hamiltonian. The absolute battery tail and
whole-controller/all-rest product defect are both in the conclusion. -/
theorem finite_conserving_phase {I : Inventory} {S : Schedule I}
    (β : ℝ) (hβ : 0 < β) (p : Driven S β) (b : Budget)
    (η ζ : ℝ) (hη : 0 < η) (hζ : 0 < ζ) (hb : Driven.Meets p b)
    (hs : SmallBudget b η) (hc : Driven.CapitalCharged p)
    (hd : ∀ r (t : Tester S r), |Driven.defect p t| ≤ 2*η) :
    ∃ (d : Engine S β) (B : Budget), Approximates d.extension p.extension ζ ∧
      MeetsBudget d B ∧ SmallBudget B (4*η+ζ) ∧
      nominalDebit d ≤ Driven.nominalDebit p+ζ ∧
      faithfulRelativeEntropy d.controller.matrix (gibbs β d.HC)/β ≤ d.capital := by
  exact PhaseProtocol.realizes β hβ p b η ζ hη hζ hb hs hc hd

end ScheduleLaw.Blueprint
