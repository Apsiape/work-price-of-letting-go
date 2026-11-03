import Proofs
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Regularization of the uniform finite-block lower bound. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace ScheduleLaw

theorem limsup_real_add_vanishing (a b : ℕ → ℝ) (hb : Vanishes b) :
    limsup (fun n => ((a n + b n : ℝ) : EReal)) atTop ≤
      limsup (fun n => (a n : EReal)) atTop := by
  have ht : Tendsto (fun n => (b n : EReal)) atTop (𝓝 (0 : EReal)) := by
    simpa using (EReal.tendsto_coe.mpr hb)
  have hl : limsup (fun n => (b n : EReal)) atTop = 0 := ht.limsup_eq
  have h := EReal.limsup_add_le (u := fun n => (a n : EReal))
    (v := fun n => (b n : EReal)) (f := atTop)
    (Or.inr (by rw [hl]; exact EReal.coe_ne_top 0))
    (Or.inr (by rw [hl]; exact EReal.coe_ne_bot 0))
  simpa only [Pi.add_apply, ← EReal.coe_add, hl, add_zero] using h

/-- No interchange of smoothing infima and limsups is used. The implementation's
own vanishing uniform error sequence is one admissible sequence in the infimum. -/
theorem regularized_converse_of_accounting {β : ℝ} (hβ : 0 < β)
    (T : TaskFamily) (d : Implementation β T)
    (haccount : ∀ n, PhysicalAccountingData (d.engine n)) :
    regularizedCost β T ≤ implementationRate d := by
  let B : ℕ → ℝ := fun n => (d.budget n).controllerEnergy + (d.budget n).absoluteTail +
    ((d.budget n).controllerEntropy + (d.budget n).batteryEntropy) / β
  have hB : Sublinear B := endpoint_budget_sublinear d.budget β d.returns
  have hfinite : ∀ n, finiteCost β (T.target n) (d.error n) ≤
      ((nominalDebit (d.engine n) + B n : ℝ) : EReal) := by
    intro n
    have h := finite_physical_lower_bound_of_accounting hβ (T.target n) (d.engine n)
      (d.error n) (d.budget n) (d.service n) (d.endpoints n) (haccount n)
    convert h using 2
    dsimp [B]
    ring
  have hnormalized : ∀ n,
      finiteCost β (T.target n) (d.error n) / ((n + 1 : ℝ) : EReal) ≤
      (((nominalDebit (d.engine n) / (n+1 : ℝ)) + B n / (n+1 : ℝ) : ℝ) : EReal) := by
    intro n
    have hh := EReal.div_le_div_right_of_nonneg
      (c := ((n+1 : ℝ) : EReal)) (by exact_mod_cast (show (0 : ℝ) ≤ n+1 by positivity))
      (hfinite n)
    simpa only [← EReal.coe_div, add_div] using hh
  unfold regularizedCost
  apply iInf_le_of_le d.error
  apply iInf_le_of_le ⟨d.error_nonneg,d.error_vanishes⟩
  calc
    limsup (fun n => finiteCost β (T.target n) (d.error n) / ((n+1 : ℝ) : EReal)) atTop
        ≤ limsup (fun n => (((nominalDebit (d.engine n) / (n+1 : ℝ)) +
          B n / (n+1 : ℝ) : ℝ) : EReal)) atTop :=
      limsup_le_limsup (Eventually.of_forall hnormalized)
    _ ≤ implementationRate d := limsup_real_add_vanishing _ _ hB

theorem optimalWork_converse_of_accounting {β : ℝ} (hβ : 0 < β)
    (T : TaskFamily)
    (haccount : ∀ d : Implementation β T, ∀ n, PhysicalAccountingData (d.engine n)) :
    regularizedCost β T ≤ optimalWork β T := by
  unfold optimalWork
  apply le_iInf
  intro d
  exact regularized_converse_of_accounting hβ T d (haccount d)

end ScheduleLaw
