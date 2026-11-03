import FactoryFamilyRates
import FactoryPreparedEnergy
import CircuitBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryUniformBounds
open History

theorem eigenvalue_abs {a : Type} [Fintype a] [DecidableEq a]
    (U : Mat a) (hU : IsUnitary U) (E : a → ℝ) (i : a) :
    |E i| ≤ ‖evolve U (diagonal (fun j => (E j : ℂ)))‖ := by
  rw [FactoryEnergy.norm_evolve _ _ hU,Matrix.l2_opNorm_diagonal]
  simpa only [Complex.norm_real,Real.norm_eq_abs] using
    (norm_le_pi_norm (fun j => (E j : ℂ)) i)

theorem spectral_gap {a : Type} [Fintype a] [DecidableEq a]
    (U : Mat a) (hU : IsUnitary U) (E : a → ℝ) (i j : a) :
    |E j-E i| ≤ 2*‖evolve U (diagonal (fun k => (E k : ℂ)))‖ := by
  exact (abs_sub _ _).trans (by linarith [eigenvalue_abs U hU E i,eigenvalue_abs U hU E j])

theorem gap_sum (β t L Λ logD logK logR Eg Ecode : ℝ)
    (hβ : 0 < β) (ht : 1 ≤ t) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ)
    (hK : 0 ≤ logK) (hKD : logK ≤ logD) (hR : logR ≤ t)
    (hD : logD=t*L+logR) (hEg : |Eg| ≤ t*Λ) (hEc : |Ecode| ≤ t*Λ) :
    |-Eg-1|+|-(logD-logK)/β|+|Eg-Ecode|+|(logD-logR)/β-1|  ≤ 
      t*(3*Λ+(2*L+1)/β+2) := by
  have hb : |-(logD-logK)/β| ≤ t*(L+1)/β := by
    rw [abs_div,abs_neg,abs_of_nonneg (sub_nonneg.mpr hKD),abs_of_pos hβ]
    exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  have h1 : |-Eg-1| ≤ t*Λ+1 := by
    calc _  ≤  |-Eg|+|(1 : ℝ)| := abs_sub _ _
         _  ≤  t*Λ+1 := by rw [abs_neg,abs_one]; linarith
  have h3 : |Eg-Ecode| ≤ 2*t*Λ := (abs_sub _ _).trans (by linarith)
  have h4 : |(logD-logR)/β-1| ≤ t*L/β+1 := by
    rw [hD,add_sub_cancel_right]
    calc _  ≤  |t*L/β|+|(1 : ℝ)| := abs_sub _ _
         _ = t*L/β+1 := by rw [abs_of_nonneg (by positivity),abs_one]
  calc _  ≤  (t*Λ+1)+t*(L+1)/β+2*t*Λ+(t*L/β+1) := by linarith
       _  ≤  t*(3*Λ+(2*L+1)/β+2) := by
         have he : t*(L+1)/β+t*L/β=t*((2*L+1)/β) := by ring
         nlinarith

theorem corrected_error (m Λ ε f δ : ℝ) (hm : 0 ≤ m) (hΛ : 0 ≤ Λ)
    (hε : 0 ≤ ε) (hf : 0 ≤ f) (hδ : f ≤ δ) (a b : ℝ)
    (ha : |a| ≤ 2*(m*Λ)*(2*ε+f)) (hb : |b| ≤ 2*(m*Λ)*f) :
    |a+b| ≤ m*(4*Λ)*(ε+δ) := by
  calc _  ≤  |a|+|b| := abs_add_le _ _
       _  ≤  2*(m*Λ)*(2*ε+f)+2*(m*Λ)*f := add_le_add ha hb
       _ = m*(4*Λ)*(ε+f) := by ring
       _  ≤  m*(4*Λ)*(ε+δ) := mul_le_mul_of_nonneg_left (by linarith : ε+f ≤ ε+δ) (by positivity)

theorem residue_eventually {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ) :
    ∀ᶠ n : ℕ in atTop, Real.log (C.residue n : ℝ) ≤ (n+1 : ℝ) := by
  have hr : ∀ᶠ n : ℕ in atTop, Real.log (C.residue n : ℝ)/(n+1 : ℝ)<1 :=
    C.residue_rate.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hr] with n hn
  simpa only [one_mul] using ((div_lt_iff₀ (by positivity : (0 : ℝ)<n+1)).mp hn).le

end ScheduleLaw.Blueprint.FactoryUniformBounds


