import Contract
import EntropyBridge
import Gibbs
import Factory
import Lift

/-! Proven finite results. No result from Challenge is imported here. -/
set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker Topology ComplexOrder
namespace ScheduleLaw

theorem entropy_of_hermitian {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Mat n) (h : ρ.IsHermitian) :
    entropy ρ = ∑ i, Real.negMulLog (h.eigenvalues i) := by
  simp [entropy, h]

theorem density_eigenvalues_sum {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Density n) : ∑ i, ρ.positive.isHermitian.eigenvalues i = 1 := by
  have h := ρ.positive.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.normalized] at h
  have hr := congrArg Complex.re h
  simpa using hr.symm

theorem density_entropy_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Density n) : 0 ≤ entropy ρ.matrix := by
  rw [entropy_of_hermitian _ ρ.positive.isHermitian]
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (ρ.positive.eigenvalues_nonneg i)
  calc ρ.positive.isHermitian.eigenvalues i
      ≤ ∑ j, ρ.positive.isHermitian.eigenvalues j :=
        Finset.single_le_sum (fun j _ => ρ.positive.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := density_eigenvalues_sum ρ

theorem energy_conserved {n : Type} [Fintype n] (U H ρ : Mat n)
    (h : Conserves U H) : energy H (evolve U ρ) = energy H ρ := by
  unfold energy evolve
  have ht : (H * (U * ρ * Uᴴ)).trace = ((Uᴴ * H * U) * ρ).trace := by
    calc (H * (U * ρ * Uᴴ)).trace = ((H * (U * ρ)) * Uᴴ).trace := by
          simp only [mul_assoc]
      _ = (Uᴴ * (H * (U * ρ))).trace := trace_mul_comm _ _
      _ = ((Uᴴ * H * U) * ρ).trace := by simp only [mul_assoc]
  rw [ht, h]

/-- Absolute nominal battery tail controls the mean debit error. This applies to
any normalized finite battery distribution, including degenerate energies. -/
theorem battery_tail_controls_mean {n : Type} [Fintype n]
    (p E : n → ℝ) (nom : ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    |(∑ i, E i * p i) - nom| ≤ ∑ i, |E i - nom| * p i := by
  have he : (∑ i, E i * p i) - nom = ∑ i, (E i - nom) * p i := by
    simp [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  rw [he]
  calc |∑ i, (E i - nom) * p i| ≤ ∑ i, |(E i - nom) * p i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |E i - nom| * p i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hp i)]

/-- Exactly the rational-algebra step of Whole-block identity, after its three
physical/entropy equalities have been supplied. -/
theorem whole_block_ledger (l : Ledger) (β : ℝ) (hβ : 0 < β) (h : l.Accounts β) :
    -l.batteryEnergy - l.controllerEnergy + (l.controllerEntropy + l.batteryEntropy) / β =
      l.handoffEnergy + (l.deviceEntropy + l.relativeEntropy + l.totalCorrelation) / β := by
  rcases h with ⟨hS, hG, hE⟩
  apply (mul_right_inj' hβ.ne').mp
  field_simp
  nlinarith

theorem ledger_lower_bound (l : Ledger) (β d u s b v : ℝ) (hβ : 0 < β)
    (ha : l.Accounts β) (hD : 0 ≤ l.relativeEntropy) (hI : 0 ≤ l.totalCorrelation)
    (hE : |l.controllerEnergy| ≤ u) (hS : |l.controllerEntropy| ≤ s)
    (hB : l.batteryEntropy ≤ b) (hW : |d + l.batteryEnergy| ≤ v) :
    LedgerBound l β d u s b v := by
  have hid := whole_block_ledger l β hβ ha
  have he := (abs_le.mp hE).1
  have hs := (abs_le.mp hS).2
  have hw := (abs_le.mp hW).1
  unfold LedgerBound Ledger.Score
  apply (mul_le_mul_iff_right₀ hβ).mp
  field_simp at hid ⊢
  nlinarith

/-- The conditional finite-block physical lower bound. The hypotheses in
PhysicalAccountingData have not yet been derived for the circuit model. -/
theorem finite_physical_lower_bound_of_accounting {I : Inventory} {S : Schedule I} {β : ℝ}
    (hβ : 0 < β) (T : Target S) (e : Engine S β) (ε : ℝ) (b : Budget)
    (service : Approximates e.extension T ε) (endpoints : MeetsBudget e b)
    (accounting : PhysicalAccountingData e) :
    finiteCost β T ε ≤ ((nominalDebit e + b.controllerEnergy + b.absoluteTail +
      (b.controllerEntropy + b.batteryEntropy) / β : ℝ) : EReal) := by
  apply iInf_le_of_le e.extension
  apply iInf_le_of_le service
  apply iSup_le
  intro r
  apply iSup_le
  intro t
  have ht := endpoints.2 r t
  have hb := battery_tail_controls_mean
    (fun j => (batteryFinal e t j j).re) e.batteryEnergy
    (e.batteryEnergy e.nominalLevel) (accounting.battery_nonneg r t)
    (accounting.battery_normalized r t)
  have hw : |nominalDebit e + (engineLedger e t).batteryEnergy| ≤ b.absoluteTail := by
    have he : nominalDebit e + (engineLedger e t).batteryEnergy =
        (∑ j, e.batteryEnergy j * (batteryFinal e t j j).re) - e.batteryEnergy e.nominalLevel := by
      simp only [nominalDebit, engineLedger, batteryEnergyChange, batteryMeanFinal]
      ring
    rw [he]
    exact hb.trans ht.2.2.2.2.2
  have hl := ledger_lower_bound (engineLedger e t) β (nominalDebit e)
    b.controllerEnergy b.controllerEntropy b.batteryEntropy b.absoluteTail hβ
    (accounting.accounts r t) (accounting.relative_nonneg r t)
    (accounting.correlation_nonneg r t) ht.2.1 ht.2.2.1 ht.2.2.2.1 hw
  have hs : score β e.extension t ≤ nominalDebit e + b.controllerEnergy + b.absoluteTail +
      (b.controllerEntropy + b.batteryEntropy) / β := by
    unfold LedgerBound Ledger.Score engineLedger at hl
    unfold score
    linarith
  exact_mod_cast hs

/-- Reuse the existing classical Gibbs proof on a matrix's spectrum. This proves
the spectral entropy bound; it is not the noncommuting quantum Gibbs principle. -/
theorem spectral_gibbs_bound {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Density n) (E : n → ℝ) :
    entropy ρ.matrix ≤ (∑ i, ρ.positive.isHermitian.eigenvalues i * E i) +
      Real.log (∑ i, Real.exp (-E i)) := by
  rw [entropy_of_hermitian _ ρ.positive.isHermitian]
  exact Gibbs.gibbs_variational _ E ρ.positive.eigenvalues_nonneg (density_eigenvalues_sum ρ)

/-- The displayed arithmetic upper cost chain really uses the imported factory
lemma. No claim of constructing a quantum factory is hidden here. -/
theorem compiler_cost_chain (a F w g' g as δ C η : ℝ)
    (hf : a - F ≤ η) (ht : F + w ≤ g' + as) (hr : g' ≤ g + δ * C) :
    a + w ≤ g + δ * C + as + η :=
  Factory.rate_chain a F w g' g as δ C η hf ht hr

theorem approximates_mono {I : Inventory} {S : Schedule I}
    {e T : Extension S} {ε η : ℝ} (h : Approximates e T ε) (hε : ε ≤ η) :
    Approximates e T η := fun r t => (h r t).trans hε

theorem finiteCost_antitone {I : Inventory} {S : Schedule I}
    (β : ℝ) (T : Target S) {ε η : ℝ} (h : ε ≤ η) :
    finiteCost β T η ≤ finiteCost β T ε := by
  unfold finiteCost
  refine le_iInf fun e => le_iInf fun he => ?_
  exact iInf_le_of_le e (iInf_le_of_le (approximates_mono he h) le_rfl)

theorem finiteCost_le_uniform_score {I : Inventory} {S : Schedule I}
    (β : ℝ) (T : Target S) (e : Extension S) (ε g : ℝ)
    (service : Approximates e T ε) (bound : ∀ r (t : Tester S r), score β e t ≤ g) :
    finiteCost β T ε ≤ (g : EReal) := by
  apply iInf_le_of_le e
  apply iInf_le_of_le service
  refine iSup_le fun r => iSup_le fun t => ?_
  exact_mod_cast bound r t

theorem endpoint_budget_sublinear (b : ℕ → Budget) (β : ℝ)
    (h : BudgetFamilyReturns b) :
    Sublinear (fun n => (b n).controllerEnergy + (b n).absoluteTail +
      ((b n).controllerEntropy + (b n).batteryEntropy) / β) := by
  rcases h with ⟨_, hu, hs, hb, _, hv⟩
  unfold Sublinear Vanishes at *
  have hh := (hu.add hv).add ((hs.add hb).div_const β)
  simp only [add_zero, zero_div] at hh
  convert hh using 1
  ext n
  simp only [add_div]
  ring

theorem bits_normalization (β : ℝ) (hβ : 0 < β) (T : TaskFamily) :
    ((Real.log 2 / β : ℝ) : EReal) * Kbeta β T = regularizedCost β T := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold Kbeta
  rw [← mul_assoc, ← EReal.coe_mul]
  have h : Real.log 2 / β * (β / Real.log 2) = 1 := by field_simp
  rw [h, EReal.coe_one, one_mul]

theorem workLaw_implies_bits (β : ℝ) (hβ : 0 < β) (T : TaskFamily) (h : WorkLaw β T) :
    WorkLawBits β T := by
  unfold WorkLawBits
  rw [bits_normalization β hβ T]
  exact h.2.1

/-- A scalar certificate for the tangent lemma's quantifier problem: with a
pure unchanged source and a faithful diagonal comparison state diag(q,1-q),
the positive relative-entropy cost cannot satisfy every s-tolerance at once. -/
theorem tangent_requires_parameter_dependent_q (q β : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hβ : 0 < β) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ -Real.log (1 - s) / β < -Real.log q / β := by
  refine ⟨1 - Real.sqrt q, ?_, ?_, ?_⟩
  · have h : Real.sqrt q < 1 := by
      calc Real.sqrt q < Real.sqrt 1 := Real.sqrt_lt_sqrt hq.le hq1
        _ = 1 := Real.sqrt_one
    linarith
  · have := Real.sqrt_pos.mpr hq
    linarith
  · have hqq : q < Real.sqrt q := (Real.lt_sqrt hq.le).mpr (by nlinarith)
    have hh := Real.log_lt_log hq hqq
    have he : 1 - (1 - Real.sqrt q) = Real.sqrt q := by ring
    rw [he]
    exact (div_lt_div_iff_of_pos_right hβ).mpr (by linarith)

end ScheduleLaw
