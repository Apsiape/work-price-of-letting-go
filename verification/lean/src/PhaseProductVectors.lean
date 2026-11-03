import PhaseProductOverlap

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseProductVectors
open PhaseVectorDistance PhaseProductOverlap
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]

def product (u : ι → κ → ℝ) (x : ι → κ) : ℝ := ∏ i,u i (x i)

theorem square_sum (u : ι → κ → ℝ) :
    (∑ x,(product u x)^2)=∏ i,∑ j,(u i j)^2 := by
  simp only [product,← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (i : ι) (j : κ) => (u i j)^2)]

theorem cross_sum (u v : ι → κ → ℝ) :
    (∑ x,product u x*product v x)=∏ i,∑ j,u i j*v i j := by
  simp only [product,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : ι) (j : κ) => u i j*v i j)]

theorem norm_difference_square (u v : ι → κ → ℝ)
    (hu : ∀ i,(∑ j,(u i j)^2)=1) (hv : ∀ i,(∑ j,(v i j)^2)=1)
    (ε : ℝ) (hδ : ∀ i,(∑ j,(u i j-v i j)^2)≤ε^2) :
    ‖vector (fun x => (product u x : ℂ))-vector (fun x => (product v x : ℂ))‖^2≤
      (Fintype.card ι : ℝ)*ε^2 := by
  let a (i : ι) := ∑ j,u i j*v i j
  have ha : ∀ i,-1≤a i ∧ a i≤1 := fun i => overlap_bounds _ _ (hu i) (hv i)
  have hlocal (i : ι) : (∑ j,(u i j-v i j)^2)=2*(1-a i) := by
    calc _ = ∑ j,((u i j)^2+(v i j)^2-2*(u i j*v i j)) :=
           Finset.sum_congr rfl (fun j _ => by ring)
         _ = _ := by
           rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hu i,hv i]
           dsimp only [a]
           ring
  have hsum : 2*(∑ i,(1-a i))≤(Fintype.card ι : ℝ)*ε^2 := by
    calc _ = ∑ i,2*(1-a i) := Finset.mul_sum _ _ _
         _ ≤ ∑ _i : ι,ε^2 := Finset.sum_le_sum (fun i _ => by rw [← hlocal]; exact hδ i)
         _ = _ := by simp
  have hnorm :
      ‖vector (fun x => (product u x : ℂ))-vector (fun x => (product v x : ℂ))‖^2=
        2*(1-∏ i,a i) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vector,PiLp.sub_apply,PiLp.toLp_apply,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
    calc _ = (∑ x,(product u x)^2)+(∑ x,(product v x)^2)-2*∑ x,product u x*product v x := by
           calc _ = ∑ x,((product u x)^2+(product v x)^2-2*(product u x*product v x)) :=
                  Finset.sum_congr rfl (fun x _ => by ring)
                _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
         _ = _ := by rw [square_sum,square_sum,cross_sum]; simp only [hu,hv,Finset.prod_const_one]; dsimp only [a]; ring
  rw [hnorm]
  exact (mul_le_mul_of_nonneg_left (product_gap a ha Finset.univ) (by norm_num)).trans hsum

theorem norm_difference (u v : ι → κ → ℝ)
    (hu : ∀ i,(∑ j,(u i j)^2)=1) (hv : ∀ i,(∑ j,(v i j)^2)=1)
    (ε : ℝ) (hε : 0≤ε) (hδ : ∀ i,(∑ j,(u i j-v i j)^2)≤ε^2) :
    ‖vector (fun x => (product u x : ℂ))-vector (fun x => (product v x : ℂ))‖≤
      ((Fintype.card ι : ℝ)+1)*ε := by
  have hs := norm_difference_square u v hu hv ε hδ
  have hr : 0≤(Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hh := mul_nonneg (show 0≤(Fintype.card ι : ℝ)^2+Fintype.card ι+1 by positivity) (sq_nonneg ε)
  have hp : 0≤((Fintype.card ι : ℝ)+1)*ε := mul_nonneg (by positivity) hε
  nlinarith [norm_nonneg (vector (fun x => (product u x : ℂ))-vector (fun x => (product v x : ℂ)))]

end ScheduleLaw.Blueprint.PhaseProductVectors
