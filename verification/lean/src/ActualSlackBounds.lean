import RareHistoryEffect
import OwnedEnergy
import CircuitBounds

/-! Exact actual-circuit entropy/energy identity and the lower flat-point
estimate. No faithful tangent reference or operational Gram factorization
is assumed to exist here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.History

def tangentHamiltonian {a : Type} [Fintype a] [DecidableEq a] (β : ℝ) (q : Density a) : Mat a :=
  (((-1/β : ℝ) : ℂ) • matrixLog q.matrix)

def sourceFreeTerm {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    (q : Density (Fin e.b)) : ℝ := faithfulRelativeEntropy e.source.matrix q.matrix / β

def physicalLinearized {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    (q : Density (Fin e.b)) {r : ℕ} (t : Tester S r) : ℝ :=
  handoff e t + energy (tangentHamiltonian β q) (bodyOutput e t - e.source.matrix)

theorem physical_score_tangent_identity {I : Inventory} {S : Schedule I} (β : ℝ)
    (e : Extension S) (q : Density (Fin e.b)) {r : ℕ} (t : Tester S r) :
    sourceFreeTerm β e q + physicalLinearized β e q t =
      score β e t + faithfulRelativeEntropy (bodyOutput e t) q.matrix / β := by
  have he (A : Mat (Fin e.b)) : energy (matrixLog q.matrix) A =
      (A * matrixLog q.matrix).trace.re := congrArg Complex.re (trace_mul_comm _ _)
  unfold physicalLinearized tangentHamiltonian
  rw [energy_observable_weight]
  change sourceFreeTerm β e q + (handoff e t + (-1/β) *
    energy (matrixLog q.matrix) (bodyOutput e t - e.source.matrix)) = _
  rw [show energy (matrixLog q.matrix) (bodyOutput e t - e.source.matrix) =
      energy (matrixLog q.matrix) (bodyOutput e t) - energy (matrixLog q.matrix) e.source.matrix from
      (energyLinear (matrixLog q.matrix)).map_sub _ _,he,he]
  unfold sourceFreeTerm faithfulRelativeEntropy score
  ring

theorem handoff_lower_bound {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : -handoffBound S ≤ handoff e t := by
  unfold handoff handoffBound
  rw [Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hr := (abs_le.mp (carrierEnergy_abs_le e t
    ((S.position (v,true)).val+1) (S.carrier v))).1
  have ha := (abs_le.mp (carrierEnergy_abs_le e t
    ((S.position (v,false)).val+1) (S.carrier v))).2
  linarith

theorem score_lower_bound {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) {r : ℕ} (t : Tester S r) : -scoreBound β e ≤ score β e t := by
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  have he := density_entropy_nonneg ρ
  have hs := density_entropy_le_log_card e.source
  simp only [Fintype.card_fin] at hs
  have hd : -Real.log e.b / β ≤ (entropy (bodyOutput e t) - entropy e.source.matrix) / β :=
    div_le_div_of_nonneg_right (by change -Real.log e.b ≤ entropy ρ.matrix - entropy e.source.matrix; linarith)
      hβ.le
  have hh := handoff_lower_bound e t
  rw [neg_div] at hd
  unfold scoreBound score
  linarith

theorem score_absolute_bound {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) {r : ℕ} (t : Tester S r) : |score β e t| ≤ scoreBound β e :=
  abs_le.mpr ⟨score_lower_bound β hβ e t,score_le_bound β hβ e r t⟩

theorem physical_free_linearized_lower {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (q : Density (Fin e.b)) (hq : q.matrix.PosDef)
    {r : ℕ} (t : Tester S r) :
    -scoreBound β e ≤ sourceFreeTerm β e q + physicalLinearized β e q t := by
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  have hd := div_nonneg (relative_entropy_nonnegative ρ q hq) hβ.le
  rw [physical_score_tangent_identity]
  exact (score_lower_bound β hβ e t).trans (le_add_of_nonneg_right hd)

/-- The numerical E9 estimate, for any actual tester once the tangent's
upper free-energy estimate has been established. This theorem does not
assert the existence of that tangent or of a linear Gram representation. -/
theorem physical_flat_slack_estimate {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (q : Density (Fin e.b)) (hq : q.matrix.PosDef) (w a : ℝ)
    (hup : sourceFreeTerm β e q + w ≤ scoreBound β e + a)
    {r : ℕ} (t : Tester S r) : w - physicalLinearized β e q t ≤ 2*scoreBound β e + a :=
  flat_slack_bound hup (physical_free_linearized_lower β hβ e q hq t)

end ScheduleLaw.History
