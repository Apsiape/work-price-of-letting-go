import FactoryReset
import FactoryDriven

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryControllerReturn
open History

def wholeState {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β)
    {z : ℕ} (t : Tester S z) :
    Mat (Fin p.c × ((Fin p.w × Fin p.r) × (Payload I × Fin z))) :=
  (finalState p.extension t).submatrix
    (fun x => (p.split.symm (x.1,x.2.1),x.2.2))
    (fun x => (p.split.symm (x.1,x.2.1),x.2.2))

theorem controller_marginal {I : Inventory} {S : Schedule I} {β : ℝ}
    (p : Driven S β) {z : ℕ} (t : Tester S z) :
    Driven.controllerFinal p t=partialRight (wholeState p t) := by
  ext i j
  simp only [Driven.controllerFinal,bodyOutput,wholeState,partialRight,submatrix_apply,
    Fintype.sum_prod_type]

theorem exact_returns {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β)
    {z : ℕ} (t : Tester S z)
    (σ : Density ((Fin p.w × Fin p.r) × (Payload I × Fin z)))
    (h : wholeState p t=p.controller.matrix ⊗ₖ σ.matrix) :
    Driven.controllerProductDefect p t=0 ∧ Driven.controllerEnergyChange p t=0 ∧
      Driven.controllerEntropyChange p t=0 := by
  have hc : Driven.controllerFinal p t=p.controller.matrix := by
    rw [controller_marginal,h,partialRight_kron,σ.normalized,one_smul]
  have hp : Driven.controllerProductDefect p t=0 := by
    change traceDistance (wholeState p t) (p.controller.matrix ⊗ₖ partialLeft (wholeState p t))=0
    rw [h,partialLeft_kron,p.controller.normalized,one_smul]
    exact W2.traceDistance_self _
  exact ⟨hp,by simp [Driven.controllerEnergyChange,hc],by simp [Driven.controllerEntropyChange,hc]⟩

end ScheduleLaw.Blueprint.FactoryControllerReturn
