import FinalBodyContact
import FlagReference

/-! Append a finite thermal flag to an actual extension and apply a full
square body contact at the final cut. The purification is the flag's
explicit retained purification from ClassicalFlag.extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

def thermalBodyContact {I : Inventory} {S : Schedule I} (e : Extension S)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (U : Mat (Fin e.b ⊕ Fin e.b)) (hU : IsUnitary U) : Extension S :=
  finalBodyContact (ClassicalFlag.extension e e p hp.le hp1.le)
    (U.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (unitary_submatrix _ hU)

theorem thermalBodyContact_bodyOutput {I : Inventory} {S : Schedule I} (e : Extension S)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (U : Mat (Fin e.b ⊕ Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    bodyOutput (thermalBodyContact e p hp hp1 U hU) t =
      (evolve U (ClassicalFlag.block (((1-p : ℝ) : ℂ) • bodyOutput e t)
        ((p : ℂ) • bodyOutput e t))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold thermalBodyContact
  rw [finalBodyContact_bodyOutput,ClassicalFlag.bodyOutput_branches]
  exact evolve_submatrix_equiv (finSumFinEquiv.symm : Fin (e.b+e.b) ≃ Fin e.b ⊕ Fin e.b) _ _

theorem thermalBodyContact_observerOutput {I : Inventory} {S : Schedule I} (e : Extension S)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (U : Mat (Fin e.b ⊕ Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    observerOutput (thermalBodyContact e p hp hp1 U hU) t = observerOutput e t := by
  unfold thermalBodyContact
  rw [finalBodyContact_observerOutput,ClassicalFlag.observerOutput_branches]
  ext i j
  simp only [add_apply,smul_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

theorem thermalBodyContact_handoff {I : Inventory} {S : Schedule I} (e : Extension S)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (U : Mat (Fin e.b ⊕ Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    handoff (thermalBodyContact e p hp hp1 U hU) t = handoff e t := by
  unfold thermalBodyContact
  rw [finalBodyContact_handoff,ClassicalFlag.handoff_branches]
  ring

theorem thermalBodyContact_sourceFreeTerm {I : Inventory} {S : Schedule I} (β : ℝ)
    (e : Extension S) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (U : Mat (Fin e.b ⊕ Fin e.b)) (hU : IsUnitary U)
    (q : Density (Fin e.b)) (hq : q.matrix.PosDef) :
    sourceFreeTerm β (thermalBodyContact e p hp hp1 U hU) (flagReference q hq p hp hp1) =
      sourceFreeTerm β e q := sourceFreeTerm_flag β e q hq p hp hp1

end ScheduleLaw.Blueprint
