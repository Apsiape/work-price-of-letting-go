import BlueprintEngine
import BlueprintDiagonal

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

structure NearOptimalFamily (β : ℝ) (T : TaskFamily) where
  extension : (n : ℕ) → Extension (T.schedule n)
  error : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ error n
  vanishes : Vanishes error
  service : ∀ n, Approximates (extension n) (T.target n) (error n)
  bound : ℕ → ℝ
  scores : ∀ n r (t : Tester (T.schedule n) r), score β (extension n) t ≤ bound n
  rate : limsup (fun n => ((bound n/(n+1 : ℝ) : ℝ) : EReal)) atTop ≤ regularizedCost β T

/-- Includes both infinite-rate branches of the diagonal selection. -/
theorem near_optimal_family (β : ℝ) (hβ : 0 < β) (T : TaskFamily) :
    Nonempty (NearOptimalFamily β T) := by
  by_cases htop : regularizedCost β T = ⊤
  · refine ⟨{
      extension := T.target
      error := fun _ => 0
      nonneg := fun _ => le_rfl
      vanishes := tendsto_const_nhds
      service := fun n => extension_approximates_self (T.target n) 0 le_rfl
      bound := fun n => scoreBound β (T.target n)
      scores := fun n => score_le_bound β hβ (T.target n)
      rate := ?_ }⟩
    rw [htop]
    exact le_top
  · obtain ⟨q,hq,hqt⟩ := ereal_upper_real_sequence (regularizedCost β T) htop
    obtain ⟨e,error,bound,h0,hvan,hservice,hscore,hrate⟩ :=
      regularized_cost_selection β hβ T q hq hqt
    exact ⟨{
      extension := e
      error := error
      nonneg := h0
      vanishes := hvan
      service := hservice
      bound := bound
      scores := hscore
      rate := hrate }⟩

theorem compiled_family_rate (β : ℝ) (hβ : 0 < β) (T : TaskFamily)
    (N : NearOptimalFamily β T) :
    ∃ d : Implementation β T, implementationRate d ≤
      limsup (fun n => ((N.bound n/(n+1 : ℝ) : ℝ) : EReal)) atTop := by
  let ν : ℕ → ℝ := fun n => 1/(n+1 : ℝ)
  have hνpos (n : ℕ) : 0 < ν n := by dsimp [ν]; positivity
  have hν : Vanishes ν := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : ∀ n, CompilerConclusion β (N.extension n) (N.bound n) (ν n) :=
    fun n => compile_pointwise β hβ (N.extension n) (N.bound n) (N.scores n) (ν n) (hνpos n)
  choose d b hs hm hb hd using hp
  have hv (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hfn : ∀ n, f n ≤ ν n) : Vanishes f :=
    squeeze_zero hf hfn hν
  have hsub (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hfn : ∀ n, f n ≤ ν n) : Sublinear f := by
    apply hv
    · intro n; exact div_nonneg (hf n) (by positivity)
    · intro n
      exact (div_le_self (hf n) (by linarith [Nat.cast_nonneg (α := ℝ) n])).trans (hfn n)
  have hreturns : BudgetFamilyReturns b := by
    refine ⟨hv _ (fun n => (hm n).1.1) (fun n => (hb n).1),
      hsub _ (fun n => (hm n).1.2.1) (fun n => (hb n).2.1),
      hsub _ (fun n => (hm n).1.2.2.1) (fun n => (hb n).2.2.1),
      hsub _ (fun n => (hm n).1.2.2.2.1) (fun n => (hb n).2.2.2.1),
      hv _ (fun n => (hm n).1.2.2.2.2.1) (fun n => (hb n).2.2.2.2.1),
      hsub _ (fun n => (hm n).1.2.2.2.2.2) (fun n => (hb n).2.2.2.2.2)⟩
  let K : Implementation β T := {
    engine := d
    error := fun n => ν n + N.error n
    error_nonneg := fun n => add_nonneg (hνpos n).le (N.nonneg n)
    error_vanishes := by simpa only [add_zero] using hν.add N.vanishes
    service := fun n => approximates_triangle (d n).extension (N.extension n) (T.target n)
      (ν n) (N.error n) (hs n) (N.service n)
    budget := b
    endpoints := hm
    returns := hreturns }
  refine ⟨K, ?_⟩
  change limsup (fun n => ((nominalDebit (d n)/(n+1 : ℝ) : ℝ) : EReal)) atTop ≤ _
  calc limsup (fun n => ((nominalDebit (d n)/(n+1 : ℝ) : ℝ) : EReal)) atTop ≤
        limsup (fun n => ((N.bound n/(n+1 : ℝ)+ν n/(n+1 : ℝ) : ℝ) : EReal)) atTop := by
         apply limsup_le_limsup (Eventually.of_forall ?_)
         intro n
         apply EReal.coe_le_coe_iff.mpr
         rw [← add_div]
         exact div_le_div_of_nonneg_right (hd n) (by positivity)
       _ ≤ limsup (fun n => ((N.bound n/(n+1 : ℝ) : ℝ) : EReal)) atTop :=
         limsup_real_add_vanishing _ _ (hsub ν (fun n => (hνpos n).le) (fun _ => le_rfl))

theorem rate_attainment (β : ℝ) (hβ : 0 < β) (T : TaskFamily) :
    ∃ d : Implementation β T, implementationRate d = regularizedCost β T := by
  obtain ⟨N⟩ := near_optimal_family β hβ T
  obtain ⟨d,hd⟩ := compiled_family_rate β hβ T N
  exact ⟨d,le_antisymm (hd.trans N.rate) (regularized_converse_from_circuit hβ T d)⟩

theorem optimal_equality_attainment (β : ℝ) (hβ : 0 < β) (T : TaskFamily) :
    optimalWork β T = regularizedCost β T ∧
      ∃ d : Implementation β T, implementationRate d = regularizedCost β T := by
  obtain ⟨d,hd⟩ := rate_attainment β hβ T
  refine ⟨le_antisymm ?_ ?_,⟨d,hd⟩⟩
  · exact (iInf_le (fun a : Implementation β T => implementationRate a) d).trans_eq hd
  · exact le_iInf (fun a => regularized_converse_from_circuit hβ T a)

end ScheduleLaw.Blueprint
