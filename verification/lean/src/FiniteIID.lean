import Proofs

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ScheduleLaw.Blueprint.FiniteIID

variable {a : Type} [Fintype a]

def weight (p : a → ℝ) (n : ℕ) (x : Fin n → a) : ℝ := ∏ k, p (x k)
def deviation (f : a → ℝ) (n : ℕ) (x : Fin n → a) : ℝ := ∑ k, f (x k)

theorem weight_sum (p : a → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    ∑ x, weight p n x = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [hp]

theorem sum_words_succ (n : ℕ) (F : (Fin (n+1) → a) → ℝ) :
    ∑ x, F x = ∑ i, ∑ y : Fin n → a, F (Fin.cons i y) := by
  let e : (a × (Fin n → a)) ≃ (Fin (n+1) → a) := {
    toFun := fun x => Fin.cons x.1 x.2
    invFun := fun x => (x 0, fun k => x k.succ)
    left_inv := by intro x; simp
    right_inv := by intro x; funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp }
  calc _ = ∑ z : a × (Fin n → a), F (e z) :=
         (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
       _ = _ := Fintype.sum_prod_type _

/-- Exact first and second moments for a finite product distribution. -/
theorem centered_moments (p f : a → ℝ) (hp : ∑ i, p i = 1)
    (hf : ∑ i, p i * f i = 0) (n : ℕ) :
    (∑ x, weight p n x * deviation f n x = 0) ∧
    (∑ x, weight p n x * (deviation f n x)^2 =
      (n : ℝ) * ∑ i, p i * (f i)^2) := by
  induction n with
  | zero => simp [weight,deviation]
  | succ n ih =>
    have hw (i : a) (y : Fin n → a) :
        weight p (n+1) (Fin.cons i y) = p i * weight p n y := by
      simp [weight,Fin.prod_univ_succ]
    have hd (i : a) (y : Fin n → a) :
        deviation f (n+1) (Fin.cons i y) = f i + deviation f n y := by
      simp [deviation,Fin.sum_univ_succ]
    have hfirst (i : a) :
        (∑ y : Fin n → a, p i * weight p n y * (f i + deviation f n y)) = p i * f i := by
      calc _ = ∑ y : Fin n → a,
            (p i * f i * weight p n y + p i * (weight p n y * deviation f n y)) := by
              apply Finset.sum_congr rfl; intro y _; ring
           _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
                            weight_sum p hp n,ih.1]; ring
    have hsecond (i : a) :
        (∑ y : Fin n → a, p i * weight p n y * (f i + deviation f n y)^2) =
          p i * (f i)^2 + p i * ((n : ℝ) * ∑ j, p j * (f j)^2) := by
      calc _ = ∑ y : Fin n → a,
            (p i * (f i)^2 * weight p n y +
              (2*p i*f i) * (weight p n y * deviation f n y) +
              p i * (weight p n y * (deviation f n y)^2)) := by
                apply Finset.sum_congr rfl; intro y _; ring
           _ = _ := by
             simp only [Finset.sum_add_distrib,← Finset.mul_sum,weight_sum p hp n,ih.1,ih.2]
             ring
    constructor
    · rw [sum_words_succ]
      simp_rw [hw,hd,hfirst]
      exact hf
    · rw [sum_words_succ]
      simp_rw [hw,hd,hsecond]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,hp]
      push_cast
      ring

/-- Finite weighted Chebyshev; zero-weight words need no positivity assumption. -/
theorem chebyshev (p f : a → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (hf : ∑ i, p i * f i = 0)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    let T := Finset.univ.filter (fun x : Fin n → a =>
      0 < weight p n x ∧ |deviation f n x| ≤ (n : ℝ)*δ)
    0 ≤ 1-∑ x ∈ T, weight p n x ∧
    1-∑ x ∈ T, weight p n x ≤ (∑ i, p i * (f i)^2)/((n : ℝ)*δ^2) := by
  classical
  dsimp only
  let T := Finset.univ.filter (fun x : Fin n → a =>
    0 < weight p n x ∧ |deviation f n x| ≤ (n : ℝ)*δ)
  have hw0 (x : Fin n → a) : 0 ≤ weight p n x := Finset.prod_nonneg (fun k _ => hp0 _)
  have hs := weight_sum p hp n
  have hmass : (∑ x ∈ T, weight p n x) ≤ 1 := by
    rw [← hs]
    exact Finset.sum_le_univ_sum_of_nonneg (fun x => hw0 x)
  have hpoint (x : Fin n → a) :
      (if x ∈ T then 0 else weight p n x) * ((n : ℝ)*δ)^2 ≤
        weight p n x * (deviation f n x)^2 := by
    by_cases hx : x ∈ T
    · simpa only [if_pos hx,zero_mul] using mul_nonneg (hw0 x) (sq_nonneg _)
    · by_cases hw : weight p n x = 0
      · simp [hw]
      · have hwp : 0 < weight p n x := lt_of_le_of_ne (hw0 x) (Ne.symm hw)
        have hnot : (n : ℝ)*δ < |deviation f n x| := by
          by_contra! h
          exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwp,h⟩)
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
        have hsq : ((n : ℝ)*δ)^2 ≤ (deviation f n x)^2 := by
          have h := (sq_le_sq₀ (by positivity : 0 ≤ (n : ℝ)*δ)
            (abs_nonneg (deviation f n x))).mpr hnot.le
          simpa only [sq_abs] using h
        simpa only [if_neg hx] using mul_le_mul_of_nonneg_left hsq (hw0 x)
  have hpartition : (∑ x : Fin n → a, if x ∈ T then 0 else weight p n x) =
      1-∑ x ∈ T, weight p n x := by
    have he (x : Fin n → a) : (if x ∈ T then 0 else weight p n x) =
        weight p n x - (if x ∈ T then weight p n x else 0) := by
      by_cases hx : x ∈ T <;> simp [hx]
    simp_rw [he]
    rw [Finset.sum_sub_distrib,hs,← Finset.sum_filter]
    simp
  have hb := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [← Finset.sum_mul,hpartition,(centered_moments p f hp hf n).2] at hb
  refine ⟨sub_nonneg.mpr hmass,?_⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos hnR (sq_pos_of_pos hδ))).mpr
  nlinarith [sq_nonneg ((n : ℝ)*δ)]

end ScheduleLaw.Blueprint.FiniteIID
