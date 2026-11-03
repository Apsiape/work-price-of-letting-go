import PhaseVectorDistance

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseProductOverlap

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem overlap_bounds (u v : κ → ℝ) (hu : (∑ j,u j^2)=1) (hv : (∑ j,v j^2)=1) :
    -1≤∑ j,u j*v j ∧ (∑ j,u j*v j)≤1 := by
  have hm : (∑ j,(u j-v j)^2)=2-2*∑ j,u j*v j := by
    calc _ = ∑ j,(u j^2+v j^2-2*(u j*v j)) := Finset.sum_congr rfl (fun j _ => by ring)
         _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hu,hv]; ring
  have hp : (∑ j,(u j+v j)^2)=2+2*∑ j,u j*v j := by
    calc _ = ∑ j,(u j^2+v j^2+2*(u j*v j)) := Finset.sum_congr rfl (fun j _ => by ring)
         _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hu,hv]; ring
  have hn : 0≤∑ j,(u j-v j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hpn : 0≤∑ j,(u j+v j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  constructor <;> nlinarith

theorem product_gap (a : ι → ℝ) (ha : ∀ i,-1≤a i ∧ a i≤1) (s : Finset ι) :
    1-∏ i∈s,a i ≤ ∑ i∈s,(1-a i) := by
  have hprod (t : Finset ι) : (∏ i∈t,a i)≤1 := by
    calc _ ≤ |∏ i∈t,a i| := le_abs_self _
         _ = ∏ i∈t,|a i| := Finset.abs_prod _ _
         _ ≤ ∏ _i∈t,(1 : ℝ) := Finset.prod_le_prod
           (fun i _ => abs_nonneg _) (fun i _ => abs_le.mpr (ha i))
         _ = 1 := by simp
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    have hh := mul_nonneg (sub_nonneg.mpr (ha i).2) (sub_nonneg.mpr (hprod s))
    nlinarith

theorem norm_reindex {a b : Type} [Fintype a] [Fintype b] (e : a ≃ b) (u : b → ℂ) :
    ‖PhaseVectorDistance.vector (fun i => u (e i))‖=‖PhaseVectorDistance.vector u‖ := by
  rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp e (fun i => ‖u i‖^2)

end ScheduleLaw.Blueprint.PhaseProductOverlap
