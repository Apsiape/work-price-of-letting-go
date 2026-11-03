import FlagAccounting

/-! Finite circuit bounds that are independent of tester memory dimension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw

theorem density_energy_abs_le {a : Type} [Fintype a] [DecidableEq a]
    (H : Mat a) (ρ : Density a) : |energy H ρ.matrix| ≤ ‖H‖ := by
  calc |energy H ρ.matrix| = |(H * ρ.matrix).trace.re| := rfl
    _ ≤ ‖(H * ρ.matrix).trace‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (H * ρ.matrix) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖H‖ * Matrix.traceNorm ρ.matrix := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = ‖H‖ := by rw [ClassicalFlag.density_traceNorm,mul_one]

theorem carrierEnergy_abs_le {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (c : Fin I.count) :
    |carrierEnergy e (run e t n) c| ≤ ‖ClassicalFlag.carrierOnPayload I c‖ := by
  have hd := run_density e t n
  let ρ : Density (Payload I) := ⟨partialRight (partialLeft (run e t n)),
    partialRight_positive (partialLeft_positive hd.1),by
      rw [partialRight_trace,partialLeft_trace]
      exact hd.2⟩
  rw [ClassicalFlag.carrierEnergy_reduced]
  exact density_energy_abs_le _ ρ

def handoffBound {I : Inventory} (S : Schedule I) : ℝ :=
  2 * ∑ v, ‖ClassicalFlag.carrierOnPayload I (S.carrier v)‖

theorem handoff_le {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : handoff e t ≤ handoffBound S := by
  unfold handoff handoffBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  have hr := (abs_le.mp (carrierEnergy_abs_le e t
    ((S.position (v,true)).val+1) (S.carrier v))).2
  have ha := (abs_le.mp (carrierEnergy_abs_le e t
    ((S.position (v,false)).val+1) (S.carrier v))).1
  linarith

theorem density_entropy_le_log_card {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Density a) : entropy ρ.matrix ≤ Real.log (Fintype.card a) := by
  rw [density_entropy_eq_library]
  simpa using Sᵥₙ_le_log_d ρ.toMState

def scoreBound {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S) : ℝ :=
  Real.log e.b / β + handoffBound S

/-- Every fixed finite extension has a finite uniform score bound, even though
the tester memory dimension remains unrestricted. -/
theorem score_le_bound {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (r : ℕ) (t : Tester S r) : score β e t ≤ scoreBound β e := by
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  have he := density_entropy_le_log_card ρ
  have hs := density_entropy_nonneg e.source
  simp only [Fintype.card_fin] at he
  unfold score scoreBound
  apply add_le_add _ (handoff_le e t)
  apply div_le_div_of_nonneg_right _ hβ.le
  linarith

end ScheduleLaw
