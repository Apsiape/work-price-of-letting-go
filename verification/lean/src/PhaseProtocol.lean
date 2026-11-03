import PhaseBudgetAssembly
import PhaseSpectralConservation
import PhaseSpectralOperational
import PhaseToleranceChoice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw.Blueprint.PhaseProtocol
open History

/-- The finite conserving phase compiler, assembled from the actual same
hardware's gates, coherent full history, six budgets and complete capital. -/
theorem realizes {I : Inventory} {S : Schedule I}
    (β : ℝ) (hβ : 0 < β) (p : Driven S β) (b : Budget)
    (η ζ : ℝ) (hη : 0 < η) (hζ : 0 < ζ) (hb : Driven.Meets p b)
    (hs : SmallBudget b η) (hc : Driven.CapitalCharged p)
    (hd : ∀ r (t : Tester S r), |Driven.defect p t| ≤ 2*η) :
    ∃ (d : Engine S β) (B : Budget), Approximates d.extension p.extension ζ ∧
      MeetsBudget d B ∧ SmallBudget B (4*η+ζ) ∧
      nominalDebit d ≤ Driven.nominalDebit p+ζ ∧
      faithfulRelativeEntropy d.controller.matrix (gibbs β d.HC)/β ≤ d.capital := by
  let rank := Fintype.card (PhaseSpectralLabels.Index p)
  let K := PhaseSpectralData.constant p
  obtain ⟨L,hL,hservice,hphysical,h2,hsmall,hcontroller,hbattery⟩ :=
    (PhaseToleranceChoice.eventually_all p.c p.w rank K (PhaseBudgetPhysical.coefficient p) ζ hζ).exists
  exact PhaseBudgetAssembly.realizes p (PhaseSpectralHardware.dim_pos p L)
    (PhaseSpectralHardware.controllerPhase p L hL) (PhaseSpectralHardware.phaseHFin p L)
    (PhaseSpectralHardware.G p L) (PhaseSpectralHardware.G_unitary p L) (PhaseSpectralHardware.G_local p L)
    rank L K η ζ (PhaseSpectralData.constant_nonneg p) hη hζ b hb hs hd
    (PhaseSpectralData.dim p L) (PhaseSpectralOperational.close p L hL)
    (PhaseSpectralConservation.conserving p L hL) hservice hphysical hcontroller hbattery

end ScheduleLaw.Blueprint.PhaseProtocol
