import FiniteTypicalRounding

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ScheduleLaw.Blueprint.FiniteIID
variable {a : Type} [Fintype a] [DecidableEq a]

/-- All per-block coding choices, with the literal integer-count rank. -/
structure PointRounding (p : a → ℝ) (n : ℕ) where
  event : Finset (Fin n → a)
  M : ℝ
  M_pos : 0 < M
  R : ℕ
  R_pos : 0 < R
  capacity : ∀ x ∈ event, ⌊M*weight p n x⌋₊ ≤ R
  rank_pos : 0 < ∑ x, if x ∈ event then ⌊M*weight p n x⌋₊ else 0

namespace PointRounding

def count {p : a → ℝ} {n : ℕ} (D : PointRounding p n) : ℕ :=
  ∑ x, if x ∈ D.event then ⌊D.M*weight p n x⌋₊ else 0

def error {p : a → ℝ} {n : ℕ} (D : PointRounding p n) : ℝ :=
  (1-∑ x ∈ D.event, weight p n x)+(D.event.card : ℝ)/D.M

theorem error_nonneg {p : a → ℝ} {n : ℕ} (D : PointRounding p n)
    (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) : 0 ≤ D.error := by
  apply add_nonneg _ (div_nonneg (Nat.cast_nonneg _) D.M_pos.le)
  apply sub_nonneg.mpr
  rw [← weight_sum p hp n]
  exact Finset.sum_le_univ_sum_of_nonneg (fun x => Finset.prod_nonneg (fun k _ => hp0 _))

end PointRounding

/-- A harmless finite-prefix code: one positive-probability word, one count. -/
theorem point_exists (p : a → ℝ) (hp : ∑ i, p i = 1)
    (n : ℕ) : Nonempty (PointRounding p n) := by
  have hx : ∃ x : Fin n → a, 0 < weight p n x := by
    by_contra! h
    have hs := weight_sum p hp n
    have hz : (∑ x : Fin n → a, weight p n x) ≤ 0 := Finset.sum_nonpos (fun x _ => h x)
    linarith
  obtain ⟨x,hx⟩ := hx
  refine ⟨{
    event := {x}
    M := (weight p n x)⁻¹
    M_pos := inv_pos.mpr hx
    R := 1
    R_pos := Nat.zero_lt_one
    capacity := ?_
    rank_pos := ?_ }⟩
  · intro y hy
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst y
    simp [inv_mul_cancel₀ hx.ne']
  · simp [inv_mul_cancel₀ hx.ne']

theorem fixed_rates (p : a → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (S δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n)
    (hloss : loss p S δ n ≤ 1/2) (hlog : Real.log 2/(n : ℝ) ≤ δ) :
    0 < rank p S δ n ∧
    |Real.log (rank p S δ n : ℝ)/(n : ℝ)-S| ≤ 2*δ ∧
    0 ≤ Real.log (residue δ n : ℝ)/(n : ℝ) ∧
    Real.log (residue δ n : ℝ)/(n : ℝ) ≤ 4*δ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM : 0 < scale S δ n := Real.exp_pos _
  have hb := rounded_rank_bounds p hp0 hp S δ n
  have hlo : scale S δ n/2 ≤ (rank p S δ n : ℝ) := by nlinarith
  have hk : 0 < (rank p S δ n : ℝ) := lt_of_lt_of_le (by positivity) hlo
  have hlog2 : Real.log 2 ≤ δ*(n : ℝ) := (div_le_iff₀ hnR).mp hlog
  have hl : (n : ℝ)*(S+2*δ)-Real.log 2 ≤ Real.log (rank p S δ n : ℝ) := by
    calc _ = Real.log (scale S δ n/2) := by
           rw [Real.log_div hM.ne' (by norm_num),scale,Real.log_exp]
         _ ≤ _ := Real.log_le_log (by positivity) hlo
  have hu : Real.log (rank p S δ n : ℝ) ≤ (n : ℝ)*(S+2*δ) := by
    simpa only [scale,Real.log_exp] using Real.log_le_log hk hb.2
  have hkl : S ≤ Real.log (rank p S δ n : ℝ)/(n : ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  have hku : Real.log (rank p S δ n : ℝ)/(n : ℝ) ≤ S+2*δ := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  have hr : 0 < residue δ n := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hrR : 0 < (residue δ n : ℝ) := by exact_mod_cast hr
  have hre : (1 : ℝ) ≤ Real.exp (3*(n : ℝ)*δ) := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (by positivity : 0 ≤ 3*(n : ℝ)*δ))
  have hrle : (residue δ n : ℝ) ≤ 2*Real.exp (3*(n : ℝ)*δ) := by
    have h := Nat.ceil_lt_add_one (Real.exp_pos (3*(n : ℝ)*δ)).le
    change (⌈Real.exp (3*(n : ℝ)*δ)⌉₊ : ℝ) ≤ _
    linarith
  have hrl : 0 ≤ Real.log (residue δ n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hr)
  have hru : Real.log (residue δ n : ℝ) ≤ Real.log 2 + 3*(n : ℝ)*δ := by
    calc _ ≤ Real.log (2*Real.exp (3*(n : ℝ)*δ)) := Real.log_le_log hrR hrle
         _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
  refine ⟨by exact_mod_cast hk,abs_le.mpr ⟨by linarith,by linarith⟩,
    div_nonneg hrl hnR.le,?_⟩
  apply (div_le_iff₀ hnR).mpr
  nlinarith

/-- For each fixed positive width, both statistical and rounding losses vanish. -/
theorem loss_tendsto (p : a → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (S : ℝ) (hS : S = ∑ i, p i * (-Real.log (p i)))
    (δ : ℝ) (hδ : 0 < δ) : Tendsto (fun m => loss p S δ (m+1)) atTop (𝓝 0) := by
  let V := ∑ i, p i * (centered p S i)^2
  have hinv : Tendsto (fun m : ℕ => 1/(m+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvariance : Tendsto (fun m : ℕ => V/((m+1 : ℝ)*δ^2)) atTop (𝓝 0) := by
    have h := hinv.const_mul (V/δ^2)
    convert h using 1
    · funext m; dsimp; simp only [div_eq_mul_inv,mul_inv_rev]; ring
    · ring
  have hn : Tendsto (fun m : ℕ => (m+1 : ℝ)) atTop atTop :=
    by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1)
  have hexp : Tendsto (fun m : ℕ => Real.exp (-(m+1 : ℝ)*δ)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.atTop_mul_const hδ)
    convert h using 1
    funext m; congr 1; ring
  have hu := hvariance.add hexp
  simp only [zero_add] at hu
  apply squeeze_zero (fun m => (loss_bounds p hp0 hp S hS δ hδ (m+1) (by omega)).1)
    (fun m => (loss_bounds p hp0 hp S hS δ hδ (m+1) (by omega)).2)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hu)

/-- Eventually one literal rounded code meets any prescribed rate/error tolerance. -/
theorem eventually_point (p : a → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (S : ℝ) (hS : S = ∑ i, p i * (-Real.log (p i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∃ D : PointRounding p (m+1),
      |Real.log (D.count : ℝ)/(m+1 : ℝ)-S| ≤ ε ∧
      Real.log (D.R : ℝ)/(m+1 : ℝ) ≤ ε ∧ D.error ≤ ε := by
  let δ := ε/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlt := loss_tendsto p hp0 hp S hS δ hδ
  have he := (tendsto_order.mp hlt).2 ε hε
  have hh := (tendsto_order.mp hlt).2 (1/2) (by norm_num)
  have hlog : Tendsto (fun m : ℕ => Real.log 2/(m+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 2)
  filter_upwards [he,hh,(tendsto_order.mp hlog).2 δ hδ] with m hem hhm hlm
  have hr := fixed_rates p hp0 hp S δ hδ (m+1) (by omega) hhm.le (by simpa only [Nat.cast_add,Nat.cast_one] using hlm.le)
  let D : PointRounding p (m+1) := {
    event := typical p S δ (m+1), M := scale S δ (m+1), M_pos := Real.exp_pos _,
    R := residue δ (m+1), R_pos := Nat.ceil_pos.mpr (Real.exp_pos _),
    capacity := count_capacity p S δ (m+1), rank_pos := hr.1 }
  refine ⟨D,?_,?_,hem.le⟩
  · change |Real.log (rank p S δ (m+1) : ℝ)/(m+1 : ℝ)-S| ≤ ε
    have h := hr.2.1
    simp only [Nat.cast_add,Nat.cast_one] at h
    exact h.trans (by dsimp [δ]; linarith)
  · change Real.log (residue δ (m+1) : ℝ)/(m+1 : ℝ) ≤ ε
    have h := hr.2.2.2
    simp only [Nat.cast_add,Nat.cast_one] at h
    exact h.trans (by dsimp [δ]; linarith)

end ScheduleLaw.Blueprint.FiniteIID
