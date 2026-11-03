import PhaseReturnStability
import FactoryEnergy
import CircuitBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.PhaseHandoffContinuity
open History
variable {I : Inventory} {S : Schedule I}

theorem carrier (e f : Extension S) {z : ℕ} (t : Tester S z) (n : ℕ) (c : Fin I.count) (δ : ℝ)
    (h : traceDistance (partialLeft (run e t n)) (partialLeft (run f t n))≤δ) :
    |carrierEnergy e (run e t n) c-carrierEnergy f (run f t n) c|≤
      2*‖ClassicalFlag.carrierOnPayload I c‖*δ := by
  rw [ClassicalFlag.carrierEnergy_reduced,ClassicalFlag.carrierEnergy_reduced]
  exact (FactoryEnergy.energy_distance _ _ _).trans
    (mul_le_mul_of_nonneg_left ((TraceMarginal.right_distance _ _).trans h) (by positivity))

theorem handoff (e f : Extension S) {z : ℕ} (t : Tester S z) (δ : ℝ)
    (h : ∀ n,n≤2*S.visits+1 →
      traceDistance (partialLeft (run e t n)) (partialLeft (run f t n))≤δ) :
    |ScheduleLaw.handoff e t-ScheduleLaw.handoff f t|≤2*handoffBound S*δ := by
  unfold ScheduleLaw.handoff
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ v : Fin S.visits,
      |(carrierEnergy e (run e t ((S.position (v,true)).val+1)) (S.carrier v)-
          carrierEnergy e (run e t ((S.position (v,false)).val+1)) (S.carrier v))-
        (carrierEnergy f (run f t ((S.position (v,true)).val+1)) (S.carrier v)-
          carrierEnergy f (run f t ((S.position (v,false)).val+1)) (S.carrier v))| :=
        Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ v : Fin S.visits,4*‖ClassicalFlag.carrierOnPayload I (S.carrier v)‖*δ := by
        apply Finset.sum_le_sum
        intro v _
        have hR := carrier e f t ((S.position (v,true)).val+1) (S.carrier v) δ
          (h _ (by have hp := (S.position (v,true)).isLt; omega))
        have hA := carrier e f t ((S.position (v,false)).val+1) (S.carrier v) δ
          (h _ (by have hp := (S.position (v,false)).isLt; omega))
        have he : (carrierEnergy e (run e t ((S.position (v,true)).val+1)) (S.carrier v)-
          carrierEnergy e (run e t ((S.position (v,false)).val+1)) (S.carrier v))-
          (carrierEnergy f (run f t ((S.position (v,true)).val+1)) (S.carrier v)-
          carrierEnergy f (run f t ((S.position (v,false)).val+1)) (S.carrier v))=
          (carrierEnergy e (run e t ((S.position (v,true)).val+1)) (S.carrier v)-
          carrierEnergy f (run f t ((S.position (v,true)).val+1)) (S.carrier v))-
          (carrierEnergy e (run e t ((S.position (v,false)).val+1)) (S.carrier v)-
          carrierEnergy f (run f t ((S.position (v,false)).val+1)) (S.carrier v)) := by ring
        rw [he]
        exact (abs_sub _ _).trans (by linarith)
       _ = _ := by simp only [handoffBound,← Finset.sum_mul,← Finset.mul_sum]; ring

end ScheduleLaw.Blueprint.PhaseHandoffContinuity
