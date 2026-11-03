/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license.
Authors: QuAIR Team

Scalar proof adapted from LeanQIT/QIT/Information/Fannes.lean in the
read-only 4.35 companion project. Source SHA256:
CD0FC0335C16661005D648504B61910393FF9DC31FEB16399AEE712F778BEB74
Only elementary scalar proofs are reused. This module imports no companion
module, state definition, entropy definition or distance definition.
The local log2 is explicitly Real.log x / Real.log 2.
-/
import FactoryEnergy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter
open scoped BigOperators NNReal Topology
universe u v
namespace ScheduleLaw.Blueprint.FiniteFannesScalar

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The source modulus `η(t)` from the HOW ordinary-entropy Fannes bound. -/
def howFannesEta (t : ℝ) : ℝ :=
  if t ≤ 1 / Real.exp 1 then
    t - t * log2 t
  else
    t + (1 / Real.exp 1) * log2 (Real.exp 1)

@[simp]
theorem howFannesEta_zero : howFannesEta 0 = 0 := by
  have h : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
  rw [howFannesEta, if_pos h]
  simp [log2]

private theorem inv_exp_one_le_one : 1 / Real.exp 1 ≤ (1 : ℝ) := by
  exact (div_le_iff₀ (Real.exp_pos 1)).2 (by
    simpa only [one_mul] using Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num))

/-- The HOW Fannes modulus is nonnegative on its physical domain. -/
theorem howFannesEta_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ howFannesEta t := by
  rw [howFannesEta]
  split_ifs with hsmall
  · have ht1 : t ≤ 1 := hsmall.trans inv_exp_one_le_one
    have hlog : log2 t ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ht ht1)
        (le_of_lt (Real.log_pos one_lt_two))
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht hlog).trans ht)
  · have hlog : 0 ≤ log2 (Real.exp 1) := by
      exact div_nonneg (Real.log_nonneg (Real.one_le_exp (by norm_num)))
        (le_of_lt (Real.log_pos one_lt_two))
    positivity

private def howFannesCorrection (t : ℝ) : ℝ :=
  if t ≤ 1 / Real.exp 1 then
    -t * log2 t
  else
    (1 / Real.exp 1) * log2 (Real.exp 1)

private theorem howFannesEta_eq_add_correction (t : ℝ) :
    howFannesEta t = t + howFannesCorrection t := by
  unfold howFannesEta howFannesCorrection
  split_ifs <;> ring

private theorem neg_mul_log2_eq_negMulLog_div (t : ℝ) :
    -t * log2 t = Real.negMulLog t / Real.log 2 := by
  simp only [log2, Real.negMulLog, div_eq_mul_inv]
  ring

private theorem log_inv_exp_one : Real.log (1 / Real.exp 1) = -1 := by
  rw [one_div, Real.log_inv, Real.log_exp]

private theorem howFannesCorrection_boundary :
    -(1 / Real.exp 1) * log2 (1 / Real.exp 1) =
      (1 / Real.exp 1) * log2 (Real.exp 1) := by
  rw [log2, log2, log_inv_exp_one, Real.log_exp]
  ring

private def howNegMulLogCorrection (t : ℝ) : ℝ :=
  if t ≤ 1 / Real.exp 1 then
    Real.negMulLog t
  else
    Real.negMulLog (1 / Real.exp 1)

private theorem howFannesCorrection_eq_negMulLogCorrection_div (t : ℝ) :
    howFannesCorrection t = howNegMulLogCorrection t / Real.log 2 := by
  unfold howFannesCorrection howNegMulLogCorrection
  split_ifs with hsmall
  · exact neg_mul_log2_eq_negMulLog_div t
  · rw [← howFannesCorrection_boundary, neg_mul_log2_eq_negMulLog_div]

private theorem concaveOn_neg_mul_log2 :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => -t * log2 t) := by
  have hscale : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
  have h := Real.concaveOn_negMulLog.smul hscale
  have heq :
      (fun t : ℝ => -t * log2 t) =
        fun t : ℝ => (Real.log 2)⁻¹ * Real.negMulLog t := by
    funext t
    rw [neg_mul_log2_eq_negMulLog_div]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  simpa [smul_eq_mul] using h

private theorem monotoneOn_negMulLog_Icc_inv_exp :
    MonotoneOn Real.negMulLog (Set.Icc (0 : ℝ) (1 / Real.exp 1)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun t : ℝ => -Real.log t - 1) (convex_Icc 0 (1 / Real.exp 1)) ?_ ?_ ?_
  · intro t _
    exact Real.continuous_negMulLog.continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) (1 / Real.exp 1) := by
      simpa [interior_Icc] using ht
    exact (Real.hasDerivAt_negMulLog ht'.1.ne').hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) (1 / Real.exp 1) := by
      simpa [interior_Icc] using ht
    have hlog : Real.log t ≤ -1 := by
      calc
        Real.log t ≤ Real.log (1 / Real.exp 1) :=
          Real.log_le_log ht'.1 ht'.2.le
        _ = -1 := log_inv_exp_one
    linarith

private theorem monotoneOn_neg_mul_log2_Icc_inv_exp :
    MonotoneOn (fun t : ℝ => -t * log2 t)
      (Set.Icc (0 : ℝ) (1 / Real.exp 1)) := by
  intro x hx y hy hxy
  change -x * log2 x ≤ -y * log2 y
  rw [neg_mul_log2_eq_negMulLog_div, neg_mul_log2_eq_negMulLog_div]
  exact div_le_div_of_nonneg_right
    (monotoneOn_negMulLog_Icc_inv_exp hx hy hxy)
    (le_of_lt (Real.log_pos one_lt_two))

private theorem antitoneOn_negMulLog_Ici_inv_exp :
    AntitoneOn Real.negMulLog (Set.Ici (1 / Real.exp 1 : ℝ)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t : ℝ => -Real.log t - 1) (convex_Ici (1 / Real.exp 1)) ?_ ?_ ?_
  · intro t _
    exact Real.continuous_negMulLog.continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioi (1 / Real.exp 1 : ℝ) := by
      simpa [interior_Ici] using ht
    exact (Real.hasDerivAt_negMulLog (ne_of_gt (lt_trans (by positivity) ht'))).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioi (1 / Real.exp 1 : ℝ) := by
      simpa [interior_Ici] using ht
    have hlog : -1 ≤ Real.log t := by
      calc
        -1 = Real.log (1 / Real.exp 1) := log_inv_exp_one.symm
        _ ≤ Real.log t := Real.log_le_log (by positivity) ht'.le
    linarith

private theorem negMulLog_le_at_inv_exp {t : ℝ} (ht : 0 ≤ t) :
    Real.negMulLog t ≤ Real.negMulLog (1 / Real.exp 1) := by
  by_cases hsmall : t ≤ 1 / Real.exp 1
  · exact monotoneOn_negMulLog_Icc_inv_exp ⟨ht, hsmall⟩
      ⟨by positivity, le_rfl⟩ hsmall
  · exact antitoneOn_negMulLog_Ici_inv_exp
      (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr (le_of_not_ge hsmall))
      (le_of_not_ge hsmall)

private theorem negMulLog_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  by_cases hx0 : x = 0
  · subst x
    simp
  by_cases hy0 : y = 0
  · subst y
    simp
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hsumpos : 0 < x + y := add_pos hxpos hypos
  have hxlog : Real.log x ≤ Real.log (x + y) :=
    Real.log_le_log hxpos (le_add_of_nonneg_right hy)
  have hylog : Real.log y ≤ Real.log (x + y) :=
    Real.log_le_log hypos (le_add_of_nonneg_left hx)
  simp only [Real.negMulLog]
  nlinarith [mul_le_mul_of_nonneg_left hxlog hx,
    mul_le_mul_of_nonneg_left hylog hy]

private theorem abs_negMulLog_sub_le_of_le_of_abs_sub_le
    {x y : ℝ} (hx0 : 0 ≤ x) (hy1 : y ≤ 1) (hxy : x ≤ y)
    (hd : |x - y| ≤ 1 / Real.exp 1) :
    |Real.negMulLog x - Real.negMulLog y| ≤ Real.negMulLog |x - y| := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hfx0 : 0 ≤ Real.negMulLog x := Real.negMulLog_nonneg hx0 (hxy.trans hy1)
  have hfy0 : 0 ≤ Real.negMulLog y := Real.negMulLog_nonneg hy0 hy1
  have hd_eq : |x - y| = y - x := abs_of_nonpos (sub_nonpos.mpr hxy) |>.trans (neg_sub x y)
  have hd0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  rw [hd_eq] at hd ⊢
  by_cases hvalues : Real.negMulLog x ≤ Real.negMulLog y
  · rw [abs_of_nonpos (sub_nonpos.mpr hvalues)]
    have hsub := negMulLog_add_le x (y - x) hx0 hd0
    rw [show x + (y - x) = y by ring] at hsub
    linarith
  · have hvalues' : Real.negMulLog y < Real.negMulLog x := lt_of_not_ge hvalues
    rw [abs_of_nonneg (sub_nonneg.mpr hvalues'.le)]
    have hxylt : x < y := lt_of_le_of_ne hxy (by
      intro h
      subst y
      exact hvalues' |>.false)
    have hxpos : 0 < x := by
      rcases hx0.eq_or_lt with rfl | hxpos
      · simp at hvalues'
        exact (not_lt_of_ge hfy0 hvalues').elim
      · exact hxpos
    obtain ⟨z, hz, hzslope⟩ :=
      exists_hasDerivAt_eq_slope Real.negMulLog (fun t : ℝ => -Real.log t - 1)
        hxylt Real.continuous_negMulLog.continuousOn
        (fun t ht => Real.hasDerivAt_negMulLog (ne_of_gt (lt_trans hxpos ht.1)))
    have hmul :
        (-Real.log z - 1) * (y - x) = Real.negMulLog y - Real.negMulLog x :=
      (eq_div_iff (sub_ne_zero.mpr hxylt.ne')).mp hzslope
    have hzlog : Real.log z ≤ 0 :=
      Real.log_nonpos (le_of_lt (lt_trans hxpos hz.1)) (hz.2.le.trans hy1)
    have hdpos : 0 < y - x := sub_pos.mpr hxylt
    have hdlog : Real.log (y - x) ≤ -1 := by
      calc
        Real.log (y - x) ≤ Real.log (1 / Real.exp 1) :=
          Real.log_le_log hdpos hd
        _ = -1 := log_inv_exp_one
    have hslope_bound : Real.log z + 1 ≤ -Real.log (y - x) := by linarith
    have hmul_bound := mul_le_mul_of_nonneg_left hslope_bound hd0
    have hdiff :
        Real.negMulLog x - Real.negMulLog y =
          (y - x) * (Real.log z + 1) := by
      nlinarith [hmul]
    calc
      Real.negMulLog x - Real.negMulLog y =
          (y - x) * (Real.log z + 1) := hdiff
      _ ≤ (y - x) * (-Real.log (y - x)) := hmul_bound
      _ = Real.negMulLog (y - x) := by
        simp only [Real.negMulLog]
        ring

private theorem abs_negMulLog_sub_le_correction
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |Real.negMulLog x - Real.negMulLog y| ≤
      if |x - y| ≤ 1 / Real.exp 1 then
        Real.negMulLog |x - y|
      else
        Real.negMulLog (1 / Real.exp 1) := by
  split_ifs with hsmall
  · rcases le_total x y with hxy | hyx
    · exact abs_negMulLog_sub_le_of_le_of_abs_sub_le hx0 hy1 hxy hsmall
    · simpa [abs_sub_comm] using
        abs_negMulLog_sub_le_of_le_of_abs_sub_le hy0 hx1 hyx (by
          simpa [abs_sub_comm] using hsmall)
  · have hfxle := negMulLog_le_at_inv_exp hx0
    have hfyle := negMulLog_le_at_inv_exp hy0
    have hfx0 := Real.negMulLog_nonneg hx0 hx1
    have hfy0 := Real.negMulLog_nonneg hy0 hy1
    rw [abs_sub_le_iff]
    constructor <;> linarith

private theorem abs_neg_mul_log2_sub_le_correction
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(-x * log2 x) - (-y * log2 y)| ≤ howFannesCorrection |x - y| := by
  have hnat := abs_negMulLog_sub_le_correction hx0 hx1 hy0 hy1
  have hscaled := div_le_div_of_nonneg_right hnat
    (le_of_lt (Real.log_pos one_lt_two))
  rw [howFannesCorrection_eq_negMulLogCorrection_div]
  unfold howNegMulLogCorrection at hscaled ⊢
  split_ifs at hscaled ⊢ with hsmall
  all_goals
    rw [neg_mul_log2_eq_negMulLog_div, neg_mul_log2_eq_negMulLog_div,
      ← sub_div, abs_div, abs_of_pos (Real.log_pos one_lt_two)]
    exact hscaled

private theorem neg_mul_log2_le_howFannesCorrection {t : ℝ} (ht : 0 ≤ t) :
    -t * log2 t ≤ howFannesCorrection t := by
  rw [neg_mul_log2_eq_negMulLog_div, howFannesCorrection_eq_negMulLogCorrection_div]
  exact div_le_div_of_nonneg_right (by
    unfold howNegMulLogCorrection
    split_ifs with hsmall
    · exact le_rfl
    · exact negMulLog_le_at_inv_exp ht)
    (le_of_lt (Real.log_pos one_lt_two))

private theorem mul_correction_div_le (n t : ℝ) (hn : 1 ≤ n) (ht : 0 ≤ t) :
    n * howFannesCorrection (t / n) ≤
      t * log2 n + howFannesCorrection t := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdiv0 : 0 ≤ t / n := div_nonneg ht hnpos.le
  by_cases havg : t / n ≤ 1 / Real.exp 1
  · rw [howFannesCorrection, if_pos havg]
    by_cases ht0 : t = 0
    · subst t
      have hcorr0 : howFannesCorrection 0 = 0 := by
        rw [howFannesCorrection, if_pos (show (0 : ℝ) ≤ 1 / Real.exp 1 by positivity)]
        simp [log2]
      simp only [zero_div, neg_zero, zero_mul, mul_zero, hcorr0, zero_add, le_refl]
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have heq :
        n * (-(t / n) * log2 (t / n)) = t * log2 n + (-t * log2 t) := by
      rw [log2, log2, log2, Real.log_div ht0 hnpos.ne']
      field_simp [hnpos.ne', (Real.log_pos one_lt_two).ne']
      ring
    rw [heq]
    exact add_le_add le_rfl (neg_mul_log2_le_howFannesCorrection ht)
  · have havglarge : 1 / Real.exp 1 < t / n := lt_of_not_ge havg
    have hcnlt : (1 / Real.exp 1) * n < t := (lt_div_iff₀ hnpos).mp havglarge
    have htlarge : 1 / Real.exp 1 < t := by
      calc
        1 / Real.exp 1 ≤ n * (1 / Real.exp 1) := by
          nlinarith [show (0 : ℝ) < 1 / Real.exp 1 by positivity]
        _ < t := by simpa [mul_comm] using hcnlt
    rw [howFannesCorrection, if_neg havg, howFannesCorrection,
      if_neg (not_le.mpr htlarge)]
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn
    have hcardLog : n - 1 ≤ n * Real.log n := Real.self_sub_one_le_mul_log hnpos.le
    have hnc : n * (1 / Real.exp 1) ≤ t := by
      simpa [mul_comm] using hcnlt.le
    have hscaledCard :
        (n - 1) * (1 / Real.exp 1) ≤
          n * Real.log n * (1 / Real.exp 1) :=
      mul_le_mul_of_nonneg_right hcardLog (by positivity)
    have hscaledT :
        n * (1 / Real.exp 1) * Real.log n ≤ t * Real.log n :=
      mul_le_mul_of_nonneg_right hnc hlogn0
    have hnat :
        (n - 1) * (1 / Real.exp 1) ≤ t * Real.log n := by
      calc
        (n - 1) * (1 / Real.exp 1) ≤
            n * Real.log n * (1 / Real.exp 1) := hscaledCard
        _ = n * (1 / Real.exp 1) * Real.log n := by ring
        _ ≤ t * Real.log n := hscaledT
    have hraw :
        n * (1 / Real.exp 1) ≤ t * Real.log n + 1 / Real.exp 1 := by
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hraw
      (le_of_lt (Real.log_pos one_lt_two))
    rw [log2, log2, Real.log_exp]
    convert hdiv using 1 <;> ring

private theorem howFannesCorrection_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ howFannesCorrection t := by
  rw [howFannesCorrection_eq_negMulLogCorrection_div]
  apply div_nonneg
  · unfold howNegMulLogCorrection
    split_ifs with hsmall
    · exact Real.negMulLog_nonneg ht (hsmall.trans inv_exp_one_le_one)
    · exact Real.negMulLog_nonneg (by positivity) inv_exp_one_le_one
  · exact le_of_lt (Real.log_pos one_lt_two)

private theorem concaveOn_howFannesCorrection :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) howFannesCorrection := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hc0 : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
  have hc_mem : (1 / Real.exp 1 : ℝ) ∈ Set.Ici 0 := hc0
  by_cases hxsmall : x ≤ 1 / Real.exp 1
  · by_cases hysmall : y ≤ 1 / Real.exp 1
    · have hzsmall : a * x + b * y ≤ 1 / Real.exp 1 := by
        nlinarith
      rw [howFannesCorrection, if_pos hxsmall, howFannesCorrection, if_pos hysmall,
        howFannesCorrection, if_pos hzsmall]
      simpa only [smul_eq_mul] using
        concaveOn_neg_mul_log2.2 hx hy ha hb hab
    · have hylarge : 1 / Real.exp 1 < y := lt_of_not_ge hysmall
      by_cases hzsmall : a * x + b * y ≤ 1 / Real.exp 1
      · let z0 : ℝ := a * x + b * (1 / Real.exp 1)
        have hxIcc : x ∈ Set.Icc (0 : ℝ) (1 / Real.exp 1) := ⟨hx, hxsmall⟩
        have hz0_nonneg : 0 ≤ z0 := by
          dsimp [z0]
          exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hc0)
        have hz0_small : z0 ≤ 1 / Real.exp 1 := by
          dsimp [z0]
          nlinarith
        have hz_nonneg : 0 ≤ a * x + b * y :=
          add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
        have hz0_le : z0 ≤ a * x + b * y := by
          dsimp [z0]
          gcongr
        have hconc := concaveOn_neg_mul_log2.2 hx hc_mem ha hb hab
        have hmono := monotoneOn_neg_mul_log2_Icc_inv_exp
          ⟨hz0_nonneg, hz0_small⟩ ⟨hz_nonneg, hzsmall⟩ hz0_le
        rw [howFannesCorrection, if_pos hxsmall, howFannesCorrection, if_neg hysmall,
          howFannesCorrection, if_pos hzsmall]
        calc
          a * (-x * log2 x) +
                b * ((1 / Real.exp 1) * log2 (Real.exp 1)) =
              a * (-x * log2 x) +
                b * (-(1 / Real.exp 1) * log2 (1 / Real.exp 1)) := by
                  rw [howFannesCorrection_boundary]
          _ ≤ -(z0) * log2 z0 := by
                simpa only [z0, smul_eq_mul] using hconc
          _ ≤ -(a * x + b * y) * log2 (a * x + b * y) := hmono
      · have hzlarge : 1 / Real.exp 1 < a * x + b * y := lt_of_not_ge hzsmall
        have hxIcc : x ∈ Set.Icc (0 : ℝ) (1 / Real.exp 1) := ⟨hx, hxsmall⟩
        have hleft := monotoneOn_neg_mul_log2_Icc_inv_exp hxIcc
          ⟨hc0, le_rfl⟩ hxsmall
        have hleft' :
            -x * log2 x ≤ (1 / Real.exp 1) * log2 (Real.exp 1) := by
          rw [← howFannesCorrection_boundary]
          exact hleft
        rw [howFannesCorrection, if_pos hxsmall, howFannesCorrection, if_neg hysmall,
          howFannesCorrection, if_neg (not_le.mpr hzlarge)]
        calc
          a * (-x * log2 x) +
                b * ((1 / Real.exp 1) * log2 (Real.exp 1)) ≤
              a * ((1 / Real.exp 1) * log2 (Real.exp 1)) +
                b * ((1 / Real.exp 1) * log2 (Real.exp 1)) :=
                  add_le_add (mul_le_mul_of_nonneg_left hleft' ha) le_rfl
          _ = (1 / Real.exp 1) * log2 (Real.exp 1) := by
                rw [← add_mul, hab, one_mul]
  · have hxlarge : 1 / Real.exp 1 < x := lt_of_not_ge hxsmall
    by_cases hysmall : y ≤ 1 / Real.exp 1
    · by_cases hzsmall : a * x + b * y ≤ 1 / Real.exp 1
      · let z0 : ℝ := a * (1 / Real.exp 1) + b * y
        have hyIcc : y ∈ Set.Icc (0 : ℝ) (1 / Real.exp 1) := ⟨hy, hysmall⟩
        have hz0_nonneg : 0 ≤ z0 := by
          dsimp [z0]
          exact add_nonneg (mul_nonneg ha hc0) (mul_nonneg hb hy)
        have hz0_small : z0 ≤ 1 / Real.exp 1 := by
          dsimp [z0]
          nlinarith
        have hz_nonneg : 0 ≤ a * x + b * y :=
          add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
        have hz0_le : z0 ≤ a * x + b * y := by
          dsimp [z0]
          gcongr
        have hconc := concaveOn_neg_mul_log2.2 hc_mem hy ha hb hab
        have hmono := monotoneOn_neg_mul_log2_Icc_inv_exp
          ⟨hz0_nonneg, hz0_small⟩ ⟨hz_nonneg, hzsmall⟩ hz0_le
        rw [howFannesCorrection, if_neg hxsmall, howFannesCorrection, if_pos hysmall,
          howFannesCorrection, if_pos hzsmall]
        calc
          a * ((1 / Real.exp 1) * log2 (Real.exp 1)) +
                b * (-y * log2 y) =
              a * (-(1 / Real.exp 1) * log2 (1 / Real.exp 1)) +
                b * (-y * log2 y) := by
                  rw [howFannesCorrection_boundary]
          _ ≤ -(z0) * log2 z0 := by
                simpa only [z0, smul_eq_mul] using hconc
          _ ≤ -(a * x + b * y) * log2 (a * x + b * y) := hmono
      · have hzlarge : 1 / Real.exp 1 < a * x + b * y := lt_of_not_ge hzsmall
        have hyIcc : y ∈ Set.Icc (0 : ℝ) (1 / Real.exp 1) := ⟨hy, hysmall⟩
        have hright := monotoneOn_neg_mul_log2_Icc_inv_exp hyIcc
          ⟨hc0, le_rfl⟩ hysmall
        have hright' :
            -y * log2 y ≤ (1 / Real.exp 1) * log2 (Real.exp 1) := by
          rw [← howFannesCorrection_boundary]
          exact hright
        rw [howFannesCorrection, if_neg hxsmall, howFannesCorrection, if_pos hysmall,
          howFannesCorrection, if_neg (not_le.mpr hzlarge)]
        calc
          a * ((1 / Real.exp 1) * log2 (Real.exp 1)) + b * (-y * log2 y) ≤
              a * ((1 / Real.exp 1) * log2 (Real.exp 1)) +
                b * ((1 / Real.exp 1) * log2 (Real.exp 1)) :=
                  add_le_add le_rfl (mul_le_mul_of_nonneg_left hright' hb)
          _ = (1 / Real.exp 1) * log2 (Real.exp 1) := by
                rw [← add_mul, hab, one_mul]
    · have hylarge : 1 / Real.exp 1 < y := lt_of_not_ge hysmall
      have hzge : 1 / Real.exp 1 ≤ a * x + b * y := by
        calc
          1 / Real.exp 1 = a * (1 / Real.exp 1) + b * (1 / Real.exp 1) := by
            rw [← add_mul, hab, one_mul]
          _ ≤ a * x + b * y :=
            add_le_add (mul_le_mul_of_nonneg_left hxlarge.le ha)
              (mul_le_mul_of_nonneg_left hylarge.le hb)
      by_cases hzsmall : a * x + b * y ≤ 1 / Real.exp 1
      · have hzeq : a * x + b * y = 1 / Real.exp 1 := le_antisymm hzsmall hzge
        rw [howFannesCorrection, if_neg hxsmall, howFannesCorrection, if_neg hysmall,
          howFannesCorrection, if_pos hzsmall, hzeq, howFannesCorrection_boundary]
        rw [← add_mul, hab, one_mul]
      · rw [howFannesCorrection, if_neg hxsmall, howFannesCorrection, if_neg hysmall,
          howFannesCorrection, if_neg hzsmall]
        rw [← add_mul, hab, one_mul]

/-- The exact HOW modulus is concave on the nonnegative half-line. -/
theorem concaveOn_howFannesEta :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) howFannesEta := by
  have hfun : howFannesEta = id + howFannesCorrection := by
    funext t
    exact howFannesEta_eq_add_correction t
  rw [hfun]
  exact (concaveOn_id (convex_Ici (0 : ℝ))).add concaveOn_howFannesCorrection

private theorem monotoneOn_howFannesCorrection :
    MonotoneOn howFannesCorrection (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hc0 : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
  by_cases hysmall : y ≤ 1 / Real.exp 1
  · have hxsmall : x ≤ 1 / Real.exp 1 := hxy.trans hysmall
    rw [howFannesCorrection, if_pos hxsmall, howFannesCorrection, if_pos hysmall]
    exact monotoneOn_neg_mul_log2_Icc_inv_exp ⟨hx, hxsmall⟩ ⟨hy, hysmall⟩ hxy
  · by_cases hxsmall : x ≤ 1 / Real.exp 1
    · rw [howFannesCorrection, if_pos hxsmall, howFannesCorrection, if_neg hysmall]
      rw [← howFannesCorrection_boundary]
      exact monotoneOn_neg_mul_log2_Icc_inv_exp
        ⟨hx, hxsmall⟩ ⟨hc0, le_rfl⟩ hxsmall
    · rw [howFannesCorrection, if_neg hxsmall, howFannesCorrection, if_neg hysmall]

/-- The HOW modulus is monotone on the nonnegative half-line. -/
theorem howFannesEta_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    howFannesEta s ≤ howFannesEta t := by
  rw [howFannesEta_eq_add_correction, howFannesEta_eq_add_correction]
  exact add_le_add hst
    (monotoneOn_howFannesCorrection hs (hs.trans hst) hst)

/-- Jensen's inequality for the HOW modulus with finite NNReal weights. -/
theorem howFannesEta_weighted_le {ι : Type v} [Fintype ι]
    (q : ι → ℝ≥0) (t : ι → ℝ)
    (hq : ∑ j, q j = 1) (ht0 : ∀ j, 0 ≤ t j) :
    ∑ j, (q j : ℝ) * howFannesEta (t j) ≤
      howFannesEta (∑ j, (q j : ℝ) * t j) := by
  classical
  have hq' : ∑ j, (q j : ℝ) = 1 := by
    simpa only [NNReal.coe_sum, NNReal.coe_one] using
      congrArg (fun x : ℝ≥0 => (x : ℝ)) hq
  have hjensen := concaveOn_howFannesEta.le_map_sum
    (t := Finset.univ) (w := fun j => (q j : ℝ)) (p := t)
    (fun j _ => NNReal.coe_nonneg (q j)) hq' (fun j _ => ht0 j)
  simpa only [Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ, Function.comp_apply,
    smul_eq_mul] using hjensen

private theorem sum_howFannesCorrection_le {ι : Type v} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, howFannesCorrection (d i) ≤
      (Fintype.card ι : ℝ) *
        howFannesCorrection ((∑ i, d i) / (Fintype.card ι : ℝ)) := by
  classical
  let n : ℝ := Fintype.card ι
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hw_sum : ∑ _i : ι, n⁻¹ = 1 := by
    simp [n, hnpos.ne']
  have hjensen := concaveOn_howFannesCorrection.le_map_sum
    (t := Finset.univ) (w := fun _i : ι => n⁻¹) (p := d)
    (fun _ _ => inv_nonneg.mpr hnpos.le) hw_sum (fun i _ => hd i)
  have hscaled := mul_le_mul_of_nonneg_left hjensen hnpos.le
  have hleft :
      n * (∑ i, n⁻¹ * howFannesCorrection (d i)) =
        ∑ i, howFannesCorrection (d i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
  have harg :
      (∑ i, n⁻¹ * d i) = (∑ i, d i) / n := by
    rw [← Finset.mul_sum]
    simp only [div_eq_mul_inv]
    ring
  simpa only [Finset.mem_univ, Function.comp_apply, smul_eq_mul, hleft, harg, n]
    using hscaled

private theorem classical_entropy_sum_dist_le_howFannes
    {ι : Type v} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hcard : 2 ≤ Fintype.card ι) :
    |(∑ i, -p i * log2 (p i)) - ∑ i, -q i * log2 (q i)| ≤
      log2 (Fintype.card ι : ℝ) *
        howFannesEta (∑ i, |p i - q i|) := by
  classical
  let d : ι → ℝ := fun i => |p i - q i|
  let t : ℝ := ∑ i, d i
  let n : ℝ := Fintype.card ι
  have hd0 : ∀ i, 0 ≤ d i := fun i => abs_nonneg _
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => hd0 i
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (hcard.trans' (by norm_num : 1 ≤ 2))
  have hpoint (i : ι) :
      |(-p i * log2 (p i)) - (-q i * log2 (q i))| ≤ howFannesCorrection (d i) :=
    abs_neg_mul_log2_sub_le_correction (hp0 i) (hp1 i) (hq0 i) (hq1 i)
  have htriangle :
      |(∑ i, -p i * log2 (p i)) - ∑ i, -q i * log2 (q i)| ≤
        ∑ i, |(-p i * log2 (p i)) - (-q i * log2 (q i))| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hpointSum :
      (∑ i, |(-p i * log2 (p i)) - (-q i * log2 (q i))|) ≤
        ∑ i, howFannesCorrection (d i) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hJensen := sum_howFannesCorrection_le d hd0
  have hdim := mul_correction_div_le n t hn1 ht0
  have hn2 : (2 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hcard
  have hlogCard : 1 ≤ log2 n := by
    unfold log2
    exact (le_div_iff₀ (Real.log_pos one_lt_two)).2 (by
      simpa only [one_mul] using Real.log_le_log (by norm_num) hn2)
  have hcorr0 : 0 ≤ howFannesCorrection t := howFannesCorrection_nonneg ht0
  calc
    |(∑ i, -p i * log2 (p i)) - ∑ i, -q i * log2 (q i)|
        ≤ ∑ i, |(-p i * log2 (p i)) - (-q i * log2 (q i))| := htriangle
    _ ≤ ∑ i, howFannesCorrection (d i) := hpointSum
    _ ≤ n * howFannesCorrection (t / n) := by simpa [n, t] using hJensen
    _ ≤ t * log2 n + howFannesCorrection t := hdim
    _ ≤ log2 n * (t + howFannesCorrection t) := by
      nlinarith [mul_le_mul_of_nonneg_right hlogCard hcorr0]
    _ = log2 (Fintype.card ι : ℝ) *
          howFannesEta (∑ i, |p i - q i|) := by
      change log2 n * (t + howFannesCorrection t) = log2 n * howFannesEta t
      rw [howFannesEta_eq_add_correction]

/-- Additive dimension dependence, needed when cache dimension grows.
The correction is not multiplied by log dimension. -/
theorem classical_entropy_additive {ι : Type v} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) (hp0 : ∀ i,0≤p i) (hp1 : ∀ i,p i≤1)
    (hq0 : ∀ i,0≤q i) (hq1 : ∀ i,q i≤1) :
    |(∑ i,Real.negMulLog (p i))-(∑ i,Real.negMulLog (q i))| ≤
      (∑ i,|p i-q i|)*Real.log (Fintype.card ι : ℝ)+
        Real.log 2*howFannesCorrection (∑ i,|p i-q i|) := by
  classical
  let t := ∑ i,|p i-q i|
  let n : ℝ := Fintype.card ι
  have hn : 1≤n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α:=ι)
  have ht : 0≤t := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hp (i : ι) : |Real.negMulLog (p i)-Real.negMulLog (q i)| ≤
      Real.log 2*howFannesCorrection |p i-q i| := by
    have h := abs_neg_mul_log2_sub_le_correction (hp0 i) (hp1 i) (hq0 i) (hq1 i)
    rw [neg_mul_log2_eq_negMulLog_div,neg_mul_log2_eq_negMulLog_div,
      ← sub_div,abs_div,abs_of_pos (Real.log_pos one_lt_two)] at h
    have h' := (div_le_iff₀ (Real.log_pos one_lt_two)).mp h
    simpa only [mul_comm] using h'
  calc _ ≤ ∑ i,|Real.negMulLog (p i)-Real.negMulLog (q i)| := by
         rw [← Finset.sum_sub_distrib]
         exact Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ i,Real.log 2*howFannesCorrection |p i-q i| := Finset.sum_le_sum (fun i _ => hp i)
       _ = Real.log 2*(∑ i,howFannesCorrection |p i-q i|) := (Finset.mul_sum _ _ _).symm
       _ ≤ Real.log 2*(n*howFannesCorrection (t/n)) :=
         mul_le_mul_of_nonneg_left (sum_howFannesCorrection_le _ (fun i => abs_nonneg _))
           (Real.log_pos one_lt_two).le
       _ ≤ Real.log 2*(t*log2 n+howFannesCorrection t) :=
         mul_le_mul_of_nonneg_left (mul_correction_div_le n t hn ht) (Real.log_pos one_lt_two).le
       _ = _ := by
         dsimp only [n,t,log2]
         field_simp [(Real.log_pos one_lt_two).ne']

/-- Natural-log entropy correction, with a fixed finite cutoff. -/
def correction (t : ℝ) : ℝ := Real.log 2*howFannesCorrection t

theorem correction_nonneg {t : ℝ} (ht : 0≤t) : 0≤correction t :=
  mul_nonneg (Real.log_pos one_lt_two).le (howFannesCorrection_nonneg ht)

theorem correction_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : correction s ≤ correction t :=
  mul_le_mul_of_nonneg_left (monotoneOn_howFannesCorrection hs (hs.trans hst) hst)
    (Real.log_pos one_lt_two).le

theorem correction_of_small {t : ℝ} (ht : t≤1/Real.exp 1) : correction t=Real.negMulLog t := by
  rw [correction,howFannesCorrection,if_pos ht,log2]
  dsimp only [Real.negMulLog]
  field_simp [(Real.log_pos one_lt_two).ne']

theorem correction_tendsto_zero : Tendsto correction (𝓝 (0 : ℝ)) (𝓝 0) := by
  have he : correction =ᶠ[𝓝 (0 : ℝ)] Real.negMulLog := by
    filter_upwards [eventually_lt_nhds (show (0 : ℝ)<1/Real.exp 1 by positivity)] with t ht
    exact correction_of_small ht.le
  have h : Tendsto Real.negMulLog (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using Real.continuous_negMulLog.continuousAt.tendsto (x:=0)
  exact h.congr' he.symm

end ScheduleLaw.Blueprint.FiniteFannesScalar
