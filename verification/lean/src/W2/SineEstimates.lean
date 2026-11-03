import W2.SequenceShifts
import BlueprintContracts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ScheduleLaw.Blueprint.W2

def sineValue (L : ℕ) (x : ℤ) : ℝ :=
  if 0 ≤ x ∧ x < L then
    Real.sqrt (2/(L+1 : ℝ))*Real.sin (Real.pi*(x+1)/(L+1 : ℝ)) else 0

theorem finite_sine_square_sum (L : ℕ) (hL : 0 < L) :
    (∑ j ∈ Finset.range L, Real.sin (((j : ℝ)+1)*(Real.pi/(L+1 : ℝ)))^2) =
      (L+1 : ℝ)/2 := by
  let θ : ℝ := Real.pi/(L+1 : ℝ)
  have hden : (0 : ℝ) < (L : ℝ)+1 := by positivity
  have hθ : 0 < θ := div_pos Real.pi_pos hden
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ hden).mpr
    have hLn : (0 : ℝ) < L := by exact_mod_cast hL
    nlinarith [Real.pi_pos]
  have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)
  have hstep (j : ℕ) :
      Real.sin ((2*((j+1 : ℕ) : ℝ)+1)*θ) - Real.sin ((2*(j : ℝ)+1)*θ) =
        2*Real.sin θ-4*Real.sin θ*Real.sin (((j : ℝ)+1)*θ)^2 := by
    rw [show (2*((j+1 : ℕ) : ℝ)+1)*θ = 2*(((j : ℝ)+1)*θ)+θ by push_cast; ring,
      show (2*(j : ℝ)+1)*θ = 2*(((j : ℝ)+1)*θ)-θ by ring,
      Real.sin_add,Real.sin_sub,Real.cos_two_mul_eq_one_sub]
    ring
  have hsum := Finset.sum_range_sub (fun j : ℕ => Real.sin ((2*(j : ℝ)+1)*θ)) L
  simp_rw [hstep] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum] at hsum
  have hend : (2*(L : ℝ)+1)*θ=2*Real.pi-θ := by
    dsimp [θ]
    field_simp [hden.ne']
    ring
  rw [hend,Real.sin_two_pi_sub] at hsum
  simp only [Nat.cast_zero,mul_zero,zero_add,one_mul,nsmul_eq_mul,Finset.card_range] at hsum
  have hz : Real.sin θ *
      (2*(∑ j ∈ Finset.range L,Real.sin (((j : ℝ)+1)*θ)^2)-((L : ℝ)+1))=0 := by
    nlinarith [hsum]
  have he := (mul_eq_zero.mp hz).resolve_left hs
  change (∑ j ∈ Finset.range L,Real.sin (((j : ℝ)+1)*θ)^2)=((L : ℝ)+1)/2
  linarith

theorem sineValue_normalized (L : ℕ) (hL : 0 < L) :
    (∑' x : ℤ, (sineValue L x)^2)=1 := by
  classical
  let s : Finset ℤ := (Finset.range L).image (fun j : ℕ => (j : ℤ))
  have hout (x : ℤ) (hx : x ∉ s) : (sineValue L x)^2=0 := by
    have ho : ¬(0 ≤ x ∧ x < (L : ℤ)) := by
      intro hi
      apply hx
      exact Finset.mem_image.mpr ⟨x.toNat,by simp only [Finset.mem_range]; omega,by omega⟩
    simp [sineValue,ho]
  rw [tsum_eq_sum hout]
  rw [Finset.sum_image (by intro a ha b hb hab; dsimp at hab; exact_mod_cast hab)]
  have hin (j : ℕ) (hj : j ∈ Finset.range L) :
      (sineValue L (j : ℤ))^2 =
        (2/(L+1 : ℝ))*Real.sin (((j : ℝ)+1)*(Real.pi/(L+1 : ℝ)))^2 := by
    have hr : (0 : ℤ) ≤ j ∧ (j : ℤ) < L := by
      simp only [Finset.mem_range] at hj
      omega
    simp only [sineValue,if_pos hr,mul_pow]
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    have ha : Real.pi*((j : ℝ)+1)/(L+1 : ℝ) =
        ((j : ℝ)+1)*(Real.pi/(L+1 : ℝ)) := by ring
    rw [ha]
  rw [Finset.sum_congr rfl hin,← Finset.mul_sum,finite_sine_square_sum L hL]
  have hd : (L+1 : ℝ) ≠ 0 := by positivity
  field_simp [hd]

theorem sineValue_sq_summable (L : ℕ) : Summable (fun x : ℤ => (sineValue L x)^2) := by
  classical
  apply summable_of_ne_finset_zero (s := (Finset.range L).image (fun j : ℕ => (j : ℤ)))
  intro x hx
  have ho : ¬(0 ≤ x ∧ x < (L : ℤ)) := by
    intro hi
    apply hx
    exact Finset.mem_image.mpr ⟨x.toNat,by simp only [Finset.mem_range]; omega,by omega⟩
  simp [sineValue,ho]

def sineSequence (L : ℕ) : RealSequence :=
  ⟨sineValue L, by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
      sineValue_sq_summable L⟩

theorem sineValue_recurrence (L : ℕ) (x : ℤ) :
    sineValue L x*(sineValue L (x-1)+sineValue L (x+1)) =
      2*Real.cos (Real.pi/(L+1 : ℝ))*(sineValue L x)^2 := by
  let θ : ℝ := Real.pi/(L+1 : ℝ)
  let c : ℝ := Real.sqrt (2/(L+1 : ℝ))
  have hclosed (y : ℤ) (hy : -1 ≤ y ∧ y ≤ (L : ℤ)) :
      sineValue L y=c*Real.sin (θ*((y : ℝ)+1)) := by
    by_cases hin : 0 ≤ y ∧ y < (L : ℤ)
    · simp only [sineValue,if_pos hin]
      change c*Real.sin (Real.pi*((y : ℝ)+1)/(L+1 : ℝ))=c*Real.sin (θ*((y : ℝ)+1))
      congr 2
      dsimp [θ]
      ring
    · have hb : y = -1 ∨ y = (L : ℤ) := by omega
      rcases hb with rfl | rfl
      · simp [sineValue]
      · have hangle : θ*((L : ℝ)+1)=Real.pi := by
          have hd : (L+1 : ℝ) ≠ 0 := by positivity
          dsimp [θ]
          field_simp [hd]
        simp [sineValue,hangle]
  by_cases hin : 0 ≤ x ∧ x < (L : ℤ)
  · rw [hclosed x (by omega),hclosed (x-1) (by omega),hclosed (x+1) (by omega)]
    push_cast
    rw [show θ*((x : ℝ)-1+1)=θ*((x : ℝ)+1)-θ by ring,
      show θ*((x : ℝ)+1+1)=θ*((x : ℝ)+1)+θ by ring,
      Real.sin_sub,Real.sin_add]
    change _=2*Real.cos θ*(c*Real.sin (θ*((x : ℝ)+1)))^2
    ring
  · have hx : sineValue L x=0 := by simp [sineValue,hin]
    rw [hx]
    ring

theorem sineSequence_step (L : ℕ) (hL : 0 < L) :
    ‖sequenceShift (sineSequence L) 1-sineSequence L‖^2 ≤ (Real.pi/(L+1 : ℝ))^2 := by
  let u := sineSequence L
  let θ : ℝ := Real.pi/(L+1 : ℝ)
  have hn : ‖u‖^2=1 := by rw [sequence_norm_sq]; exact sineValue_normalized L hL
  have hadj : inner ℝ u (sequenceShift u (-1))=inner ℝ u (sequenceShift u 1) := by
    rw [← sequenceShift_inner]
    exact real_inner_comm _ _
  have hinner : inner ℝ u (sequenceShift u 1+sequenceShift u (-1))=2*Real.cos θ := by
    simp only [lp.inner_eq_tsum,Real.inner_apply]
    change (∑' x : ℤ,sineValue L x*(sineValue L (x-1)+sineValue L (x-(-1))))=2*Real.cos θ
    simp_rw [sub_neg_eq_add,sineValue_recurrence]
    rw [tsum_mul_left,sineValue_normalized L hL,mul_one]
  rw [inner_add_right,hadj] at hinner
  have hi : inner ℝ (sequenceShift u 1) u=Real.cos θ := by
    rw [real_inner_comm]
    linarith
  have heq : ‖sequenceShift u 1-u‖^2=2-2*Real.cos θ := by
    rw [norm_sub_sq_real,sequenceShift_norm,hn,hi]
    ring
  rw [heq]
  have hc := Real.cos_two_mul_eq_one_sub (θ/2)
  rw [show 2*(θ/2)=θ by ring] at hc
  have hs := Real.sin_sq_le_sq (x := θ/2)
  change 2-2*Real.cos θ ≤ θ^2
  nlinarith [hc,hs]

theorem sineValue_shift_bound (L : ℕ) (hL : 0 < L) (k : ℤ) :
    (∑' x : ℤ,(sineValue L (x-k)-sineValue L x)^2) ≤
      (Real.pi*(|k| : ℤ)/(L+1 : ℝ))^2 := by
  let u := sineSequence L
  change (∑' x : ℤ,((sequenceShift u k-u) x)^2) ≤ _
  rw [← sequence_norm_sq]
  calc ‖sequenceShift u k-u‖^2
      ≤ (((|k| : ℤ) : ℝ)*‖sequenceShift u 1-u‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (sequenceShift_sub_norm u k) 2
    _ = (((|k| : ℤ) : ℝ)^2)*‖sequenceShift u 1-u‖^2 := mul_pow _ _ _
    _ ≤ (((|k| : ℤ) : ℝ)^2)*(Real.pi/(L+1 : ℝ))^2 :=
      mul_le_mul_of_nonneg_left (sineSequence_step L hL) (sq_nonneg _)
    _ = (Real.pi*(|k| : ℤ)/(L+1 : ℝ))^2 := by ring

end ScheduleLaw.Blueprint.W2
