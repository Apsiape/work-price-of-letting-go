import BlueprintContracts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder Topology
namespace ScheduleLaw.Blueprint

def diagonalIndex (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k=0 ∨ N k ≤ n) n

theorem diagonalIndex_spec (N : ℕ → ℕ) (n : ℕ) :
    diagonalIndex N n=0 ∨ N (diagonalIndex N n) ≤ n := by
  exact Nat.findGreatest_spec (P := fun k => k=0 ∨ N k ≤ n) (Nat.zero_le n) (Or.inl rfl)

theorem diagonalIndex_tendsto (N : ℕ → ℕ) : Tendsto (diagonalIndex N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  let j := max k 1
  filter_upwards [eventually_ge_atTop (max j (N j))] with n hn
  have hj : j ≤ n := (le_max_left _ _).trans hn
  have hNj : N j ≤ n := (le_max_right _ _).trans hn
  exact (le_max_left k 1).trans (Nat.le_findGreatest hj (Or.inr hNj))

theorem ereal_upper_real_sequence (L : EReal) (hne : L ≠ ⊤) :
    ∃ q : ℕ → ℝ, (∀ j, L < (q j : EReal)) ∧
      Tendsto (fun j => (q j : EReal)) atTop (𝓝 L) := by
  induction L using EReal.rec with
  | bot =>
      refine ⟨fun j => -(j : ℝ),fun j => EReal.bot_lt_coe _,?_⟩
      exact EReal.tendsto_coe_nhds_bot_iff.mpr
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  | coe x =>
      refine ⟨fun j => x+1/(j+1 : ℝ),?_,?_⟩
      · intro j
        apply EReal.coe_lt_coe_iff.mpr
        have h : (0 : ℝ) < 1/(j+1 : ℝ) := by positivity
        linarith
      · apply EReal.tendsto_coe.mpr
        simpa only [add_zero] using
          (tendsto_const_nhds (x := x)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  | top => exact (hne rfl).elim

theorem extension_approximates_self {I : Inventory} {S : Schedule I}
    (e : Extension S) (ε : ℝ) (hε : 0 ≤ ε) : Approximates e e ε := by
  intro r t
  simpa only [traceDistance, sub_self, ClassicalFlag.traceNorm_eq_library,
    Matrix.traceNorm_zero, zero_div] using hε

theorem finite_cost_lt_real {I : Inventory} {S : Schedule I}
    (β : ℝ) (T : Target S) (ε g : ℝ) (h : finiteCost β T ε < (g : EReal)) :
    ∃ e : Extension S, Approximates e T ε ∧ ∀ r (t : Tester S r), score β e t ≤ g := by
  unfold finiteCost at h
  obtain ⟨e,he⟩ := iInf_lt_iff.mp h
  obtain ⟨hs,hg⟩ := iInf_lt_iff.mp he
  refine ⟨e,hs,?_⟩
  intro r t
  have hi : (score β e t : EReal) ≤ ⨆ u : Tester S r, (score β e u : EReal) :=
    le_iSup (fun u : Tester S r => (score β e u : EReal)) t
  have ho : (⨆ u : Tester S r, (score β e u : EReal)) ≤
      ⨆ s : ℕ, ⨆ u : Tester S s, (score β e u : EReal) :=
    le_iSup (fun s : ℕ => ⨆ u : Tester S s, (score β e u : EReal)) r
  have ht : (score β e t : EReal) < (g : EReal) :=
    hi.trans_lt (ho.trans_lt hg)
  exact (EReal.coe_lt_coe_iff.mp ht).le

/-- Diagonalize the smoothing sequence and the finite extension together.
The limiting cost may be negative infinity; no finite-rate hypothesis is used. -/
theorem regularized_cost_selection (β : ℝ) (hβ : 0 < β) (T : TaskFamily)
    (q : ℕ → ℝ) (hq : ∀ j, regularizedCost β T < (q j : EReal))
    (hqt : Tendsto (fun j => (q j : EReal)) atTop (𝓝 (regularizedCost β T))) :
    ∃ (e : (n : ℕ) → Extension (T.schedule n)) (error bound : ℕ → ℝ),
      (∀ n, 0 ≤ error n) ∧ Vanishes error ∧
      (∀ n, Approximates (e n) (T.target n) (error n)) ∧
      (∀ n r (t : Tester (T.schedule n) r), score β (e n) t ≤ bound n) ∧
      limsup (fun n => ((bound n/(n+1 : ℝ) : ℝ) : EReal)) atTop ≤ regularizedCost β T := by
  have hselect : ∀ j, ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Vanishes ε ∧
      limsup (fun n => finiteCost β (T.target n) (ε n) / ((n+1 : ℝ) : EReal)) atTop < (q j : EReal) := by
    intro j
    have h := hq j
    unfold regularizedCost at h
    obtain ⟨ε,hε⟩ := iInf_lt_iff.mp h
    obtain ⟨hvalid,hlim⟩ := iInf_lt_iff.mp hε
    exact ⟨ε,hvalid.1,hvalid.2,hlim⟩
  choose ε hnonneg hvan hlim using hselect
  have hstage : ∀ j, ∃ N : ℕ, ∀ n, N ≤ n →
      ε j n ≤ 1/(j+1 : ℝ) ∧
        finiteCost β (T.target n) (ε j n) / ((n+1 : ℝ) : EReal) < (q j : EReal) := by
    intro j
    have herr : ∀ᶠ n : ℕ in atTop, ε j n ≤ 1/(j+1 : ℝ) :=
      ((tendsto_order.mp (hvan j)).2 _ (by positivity)).mono (fun _ h => h.le)
    exact eventually_atTop.mp (herr.and (eventually_lt_of_limsup_lt (hlim j)))
  choose N hN using hstage
  let index := diagonalIndex N
  let error : ℕ → ℝ := fun n => if index n=0 then 0 else ε (index n) n
  let bound : ℕ → ℝ := fun n => if index n=0 then scoreBound β (T.target n) else q (index n)*(n+1 : ℝ)
  have hindex : Tendsto index atTop atTop := diagonalIndex_tendsto N
  have hn (n : ℕ) (h : index n ≠ 0) : N (index n) ≤ n :=
    (diagonalIndex_spec N n).resolve_left h
  have herror0 (n : ℕ) : 0 ≤ error n := by
    dsimp only [error]
    split_ifs
    · exact le_rfl
    · exact hnonneg _ _
  have herror (n : ℕ) : error n ≤ 1/(index n+1 : ℝ) := by
    dsimp only [error]
    split_ifs with hz
    · positivity
    · exact (hN (index n) n (hn n hz)).1
  have herrorlim : Vanishes error :=
    squeeze_zero herror0 herror (tendsto_one_div_add_atTop_nhds_zero_nat.comp hindex)
  have hp : ∀ n, ∃ e : Extension (T.schedule n), Approximates e (T.target n) (error n) ∧
      ∀ r (t : Tester (T.schedule n) r), score β e t ≤ bound n := by
    intro n
    by_cases hz : index n=0
    · refine ⟨T.target n,?_,?_⟩
      · exact extension_approximates_self _ _ (herror0 n)
      · simpa only [bound,if_pos hz] using score_le_bound β hβ (T.target n)
    · have hcost := (hN (index n) n (hn n hz)).2
      have hden : (0 : EReal) < ((n+1 : ℝ) : EReal) := EReal.coe_pos.mpr (by positivity)
      have hraw := (EReal.div_lt_iff hden (EReal.coe_ne_top _)).mp hcost
      rw [← EReal.coe_mul] at hraw
      simpa only [error,bound,if_neg hz] using
        finite_cost_lt_real β (T.target n) (ε (index n) n) (q (index n)*(n+1 : ℝ)) hraw
  choose e hs hscore using hp
  refine ⟨e,error,bound,herror0,herrorlim,hs,hscore,?_⟩
  have hqlim := (hqt.comp hindex).limsup_eq
  calc limsup (fun n => ((bound n/(n+1 : ℝ) : ℝ) : EReal)) atTop ≤
        limsup (fun n => (q (index n) : EReal)) atTop := by
         have hcompare : ∀ᶠ n : ℕ in atTop,
             ((bound n/(n+1 : ℝ) : ℝ) : EReal) ≤ (q (index n) : EReal) := by
           filter_upwards [hindex.eventually (eventually_gt_atTop 0)] with n hn0
           have hz : index n ≠ 0 := Nat.ne_of_gt hn0
           simp only [bound,if_neg hz,mul_div_cancel_right₀ (q (index n)) (by positivity : (n+1 : ℝ) ≠ 0)]
           exact le_rfl
         exact limsup_le_limsup hcompare
       _ = regularizedCost β T := hqlim

end ScheduleLaw.Blueprint
