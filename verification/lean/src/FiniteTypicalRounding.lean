import FiniteIID
import BlueprintDiagonal

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ScheduleLaw.Blueprint.FiniteIID

variable {a : Type} [Fintype a] [DecidableEq a]

def centered (p : a → ℝ) (S : ℝ) (i : a) : ℝ := -Real.log (p i)-S

def typical (p : a → ℝ) (S δ : ℝ) (n : ℕ) : Finset (Fin n → a) :=
  Finset.univ.filter (fun x =>
    0 < weight p n x ∧ |deviation (centered p S) n x| ≤ (n : ℝ)*δ)

def scale (S δ : ℝ) (n : ℕ) : ℝ := Real.exp ((n : ℝ)*(S+2*δ))
def residue (δ : ℝ) (n : ℕ) : ℕ := ⌈Real.exp (3*(n : ℝ)*δ)⌉₊
def rank (p : a → ℝ) (S δ : ℝ) (n : ℕ) : ℕ :=
  ∑ x, if x ∈ typical p S δ n then ⌊scale S δ n * weight p n x⌋₊ else 0

def loss (p : a → ℝ) (S δ : ℝ) (n : ℕ) : ℝ :=
  (1-∑ x ∈ typical p S δ n, weight p n x)+((typical p S δ n).card : ℝ)/scale S δ n

omit [DecidableEq a] in
theorem centered_mean (p : a → ℝ) (S : ℝ) (hp : ∑ i, p i = 1)
    (hS : S = ∑ i, p i * (-Real.log (p i))) : ∑ i, p i * centered p S i = 0 := by
  simp only [centered,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  rw [hp,← hS]
  ring

omit [Fintype a] [DecidableEq a] in
theorem deviation_log (p : a → ℝ) (S : ℝ) (n : ℕ) (x : Fin n → a)
    (hx : weight p n x ≠ 0) :
    deviation (centered p S) n x = -Real.log (weight p n x)-(n : ℝ)*S := by
  have hne : ∀ k ∈ (Finset.univ : Finset (Fin n)), p (x k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hx
  simp only [deviation,centered,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [weight,Real.log_prod hne]

omit [DecidableEq a] in
theorem typical_envelope (p : a → ℝ) (S δ : ℝ) (n : ℕ)
    (x : Fin n → a) (hx : x ∈ typical p S δ n) :
    Real.exp (-(n : ℝ)*(S+δ)) ≤ weight p n x ∧
      weight p n x ≤ Real.exp (-(n : ℝ)*(S-δ)) := by
  have h := (Finset.mem_filter.mp hx).2
  have hd := abs_le.mp h.2
  rw [deviation_log p S n x h.1.ne'] at hd
  constructor
  · rw [← Real.exp_log h.1]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_log h.1]
    exact Real.exp_le_exp.mpr (by linarith)

theorem typical_card (p : a → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (S δ : ℝ) (n : ℕ) : (typical p S δ n).card ≤ Real.exp ((n : ℝ)*(S+δ)) := by
  have hw0 (x : Fin n → a) : 0 ≤ weight p n x := Finset.prod_nonneg (fun k _ => hp0 _)
  have hmass : (∑ x ∈ typical p S δ n, weight p n x) ≤ 1 := by
    rw [← weight_sum p hp n]
    exact Finset.sum_le_univ_sum_of_nonneg hw0
  have hb : ((typical p S δ n).card : ℝ)*Real.exp (-(n : ℝ)*(S+δ)) ≤ 1 := by
    calc _ = ∑ _x ∈ typical p S δ n, Real.exp (-(n : ℝ)*(S+δ)) := by simp
         _ ≤ ∑ x ∈ typical p S δ n, weight p n x :=
           Finset.sum_le_sum (fun x hx => (typical_envelope p S δ n x hx).1)
         _ ≤ 1 := hmass
  have h := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((n : ℝ)*(S+δ))).le
  have he : Real.exp (-(n : ℝ)*(S+δ))*Real.exp ((n : ℝ)*(S+δ)) = 1 := by
    rw [← Real.exp_add]
    have hz : -(n : ℝ)*(S+δ)+(n : ℝ)*(S+δ) = 0 := by ring
    rw [hz,Real.exp_zero]
  simpa only [mul_assoc,he,mul_one,one_mul] using h

theorem count_capacity (p : a → ℝ) (S δ : ℝ) (n : ℕ) (x : Fin n → a)
    (hx : x ∈ typical p S δ n) :
    ⌊scale S δ n * weight p n x⌋₊ ≤ residue δ n := by
  apply Nat.floor_le_of_le
  calc scale S δ n * weight p n x ≤
        scale S δ n * Real.exp (-(n : ℝ)*(S-δ)) :=
          mul_le_mul_of_nonneg_left (typical_envelope p S δ n x hx).2 (Real.exp_pos _).le
       _ = Real.exp (3*(n : ℝ)*δ) := by
         unfold scale; rw [← Real.exp_add]; congr 1; ring
       _ ≤ _ := Nat.le_ceil _

theorem rounded_rank_bounds (p : a → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (S δ : ℝ) (n : ℕ) :
    (1-loss p S δ n)*scale S δ n ≤ (rank p S δ n : ℝ) ∧
      (rank p S δ n : ℝ) ≤ scale S δ n := by
  have hM : 0 < scale S δ n := Real.exp_pos _
  have hcast : (rank p S δ n : ℝ) =
      ∑ x ∈ typical p S δ n, (⌊scale S δ n*weight p n x⌋₊ : ℝ) := by
    simp only [rank,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [hcast]
  constructor
  · calc _ = ∑ x ∈ typical p S δ n, (scale S δ n*weight p n x-1) := by
           simp only [loss,Finset.sum_sub_distrib,← Finset.mul_sum]
           simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
           field_simp [hM.ne']
           ring
         _ ≤ _ := Finset.sum_le_sum (fun x _ => by linarith [Nat.lt_floor_add_one (scale S δ n*weight p n x)])
  · calc _ ≤ ∑ x ∈ typical p S δ n, scale S δ n*weight p n x :=
           Finset.sum_le_sum (fun x _ => Nat.floor_le (mul_nonneg hM.le
             (Finset.prod_nonneg (fun k _ => hp0 _))))
         _ ≤ scale S δ n * (∑ x : Fin n → a, weight p n x) := by
           rw [Finset.mul_sum]
           exact Finset.sum_le_univ_sum_of_nonneg (fun x => mul_nonneg hM.le
             (Finset.prod_nonneg (fun k _ => hp0 _)))
         _ = _ := by rw [weight_sum p hp n,mul_one]

theorem loss_bounds (p : a → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (S : ℝ) (hS : S = ∑ i, p i * (-Real.log (p i)))
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) :
    0 ≤ loss p S δ n ∧ loss p S δ n ≤
      (∑ i, p i * (centered p S i)^2)/((n : ℝ)*δ^2)+Real.exp (-(n : ℝ)*δ) := by
  have hcheb := chebyshev p (centered p S) hp0 hp (centered_mean p S hp hS) n hn δ hδ
  change 0 ≤ 1-∑ x ∈ typical p S δ n, weight p n x ∧
    1-∑ x ∈ typical p S δ n, weight p n x ≤ _ at hcheb
  have hround : ((typical p S δ n).card : ℝ)/scale S δ n ≤ Real.exp (-(n : ℝ)*δ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    calc _ ≤ Real.exp ((n : ℝ)*(S+δ)) := typical_card p hp0 hp S δ n
         _ = Real.exp (-(n : ℝ)*δ)*scale S δ n := by
           unfold scale; rw [← Real.exp_add]; congr 1; ring
  constructor
  · exact add_nonneg hcheb.1 (div_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  · exact add_le_add hcheb.2 hround

end ScheduleLaw.Blueprint.FiniteIID
