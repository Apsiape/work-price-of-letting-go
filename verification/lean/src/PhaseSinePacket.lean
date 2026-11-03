import PhaseVectorDistance
import W2.SineEstimates

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Topology
namespace ScheduleLaw.Blueprint.PhaseSinePacket
open PhaseVectorDistance

theorem box_sum (L : ℕ) (f : ℤ → ℝ)
    (hf : ∀ x, x < -2 ∨ (L : ℤ)+1 < x → f x=0) :
    (∑ i : Fin (L+4),f ((i.val : ℤ)-2))=∑' x : ℤ,f x := by
  rw [tsum_eq_sum (s:=Finset.Icc (-2) ((L : ℤ)+1)) (fun x hx => hf x (by
    simp only [Finset.mem_Icc,not_and_or,not_le] at hx
    exact hx))]
  apply Finset.sum_bij (fun i _ => (i.val : ℤ)-2)
  · intro i _
    simp only [Finset.mem_Icc]
    have hi := i.isLt
    omega
  · intro i _ j _ h
    apply Fin.ext
    omega
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    refine ⟨⟨(x+2).toNat,by omega⟩,Finset.mem_univ _,?_⟩
    change (((x+2).toNat : ℤ)-2)=x
    omega
  · intro i _
    rfl

def scalar (L : ℕ) (δ : ℤ) : Fin (L+4) → ℂ :=
  fun i => (W2.sineValue L ((i.val : ℤ)-2-δ) : ℂ)

theorem outside_zero (L : ℕ) (δ x : ℤ) (hδ : -1≤δ ∧ δ≤1)
    (hx : x < -2 ∨ (L : ℤ)+1<x) : W2.sineValue L (x-δ)=0 := by
  unfold W2.sineValue
  rw [if_neg (by omega)]

theorem scalar_norm (L : ℕ) (hL : 0<L) (δ : ℤ) (hδ : -1≤δ ∧ δ≤1) :
    ‖vector (scalar L δ)‖=1 := by
  have hs : (∑ i : Fin (L+4),(W2.sineValue L ((i.val : ℤ)-2-δ))^2)=1 := by
    rw [box_sum L (fun x => (W2.sineValue L (x-δ))^2) (fun x hx => by
      change (W2.sineValue L (x-δ))^2=0
      rw [outside_zero L δ x hδ hx,zero_pow (by decide : (2 : ℕ)≠0)])]
    calc _ = ∑' x : ℤ,(W2.sineValue L x)^2 := (Equiv.subRight δ).tsum_eq _
         _ = 1 := W2.sineValue_normalized L hL
  have hn : ‖vector (scalar L δ)‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [vector,scalar,PiLp.toLp_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hs
  nlinarith [norm_nonneg (vector (scalar L δ))]

theorem scalar_difference (L : ℕ) (hL : 0<L) (δ : ℤ) (hδ : -1≤δ ∧ δ≤1) :
    ‖vector (scalar L δ)-vector (scalar L 0)‖ ≤ Real.pi/(L+1 : ℝ) := by
  have hs : ‖vector (scalar L δ)-vector (scalar L 0)‖^2=
      ∑' x : ℤ,(W2.sineValue L (x-δ)-W2.sineValue L x)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vector,scalar,PiLp.sub_apply,PiLp.toLp_apply,sub_zero,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
    apply box_sum L (fun x => (W2.sineValue L (x-δ)-W2.sineValue L x)^2)
    intro x hx
    change (W2.sineValue L (x-δ)-W2.sineValue L x)^2=0
    have hz := outside_zero L 0 x (by omega) hx
    simp only [sub_zero] at hz
    rw [outside_zero L δ x hδ hx,hz]
    norm_num
  have hb := W2.sineValue_shift_bound L hL δ
  have hd : |(δ : ℝ)|≤1 := by exact_mod_cast (abs_le.mpr hδ)
  have hp : 0≤Real.pi/(L+1 : ℝ) := by positivity
  push_cast at hb
  have he : Real.pi*|(δ : ℝ)|/(L+1 : ℝ)=(Real.pi/(L+1 : ℝ))*|(δ : ℝ)| := by ring
  rw [he] at hb
  have hq : (Real.pi/(L+1 : ℝ))*|(δ : ℝ)| ≤ Real.pi/(L+1 : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hp
  have hsq := pow_le_pow_left₀ (mul_nonneg hp (abs_nonneg (δ : ℝ))) hq 2
  nlinarith [norm_nonneg (vector (scalar L δ)-vector (scalar L 0)),
    mul_nonneg hp (abs_nonneg (δ : ℝ))]

end ScheduleLaw.Blueprint.PhaseSinePacket
