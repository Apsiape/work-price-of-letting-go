import FactoryControllerReturn
import FactoryBattery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryDrivenBudgets
open History

def batteryDensity {I : Inventory} {S : Schedule I} {β : ℝ}
    (p : Driven S β) {z : ℕ} (t : Tester S z) : Density (Fin p.w) := by
  have hb := bodyOutput_density p.extension t
  exact ⟨Driven.batteryFinal p t,
    partialRight_positive (partialLeft_positive (hb.1.submatrix p.split.symm)),by
      unfold Driven.batteryFinal Driven.batteryReservoirFinal
      rw [partialRight_trace,partialLeft_trace,submatrix_trace_equiv,hb.2]⟩

def budget (η f M : ℝ) : Budget := ⟨0,0,0,η,f,M*f⟩

/-- All six actual budgets follow from complete controller return, the actual
nominal battery probability, and a bound on every battery energy deviation. -/
theorem meets {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β)
    (η f M : ℝ) (hη : 0 < η) (hf : 0 ≤ f) (hM : 0 ≤ M)
    (hgap : ∀ j,|p.batteryEnergy j-p.batteryEnergy p.nominalLevel| ≤ M)
    (hreturn : ∀ z (t : Tester S z),
      ∃ σ : Density ((Fin p.w × Fin p.r) × (Payload I × Fin z)),
        FactoryControllerReturn.wholeState p t=p.controller.matrix ⊗ₖ σ.matrix) :
    ∃ ε : ℝ,0 < ε ∧
      ((∀ z (t : Tester S z),
        1-(Driven.batteryFinal p t p.nominalLevel p.nominalLevel).re ≤ min ε f) →
        Driven.Meets p (budget η f M)) := by
  obtain ⟨ε,hε,hent⟩ := FactoryBattery.entropy_tolerance p.nominalLevel η hη
  refine ⟨ε,hε,fun hfail => ?_⟩
  refine ⟨⟨le_rfl,le_rfl,le_rfl,hη.le,hf,mul_nonneg hM hf⟩,?_⟩
  intro z t
  obtain ⟨σ,hσ⟩ := hreturn z t
  obtain ⟨hp,he,hs⟩ := FactoryControllerReturn.exact_returns p t σ hσ
  have hfε : 1-(Driven.batteryFinal p t p.nominalLevel p.nominalLevel).re ≤ ε :=
    (hfail z t).trans (min_le_left _ _)
  have hff : 1-(Driven.batteryFinal p t p.nominalLevel p.nominalLevel).re ≤ f :=
    (hfail z t).trans (min_le_right _ _)
  refine ⟨by simp [hp,budget],by simp [he,budget],
    by simp [hs,budget],hent (batteryDensity p t) hfε,hff,?_⟩
  exact (FactoryBattery.absolute_tail (batteryDensity p t) p.batteryEnergy
    p.nominalLevel M hgap).trans (mul_le_mul_of_nonneg_left hff hM)

end ScheduleLaw.Blueprint.FactoryDrivenBudgets
