import CacheFactoryBody
import FactoryControllerReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCacheMarginal
open History CacheFactoryBody
variable {d m : ℕ} {β : ℝ} {τ q : Density (Fin d)}

abbrev Remaining (F : Formation β τ q m) := Fin F.hardware.w × Fin F.aux

def restFrame (F : Formation β τ q m) :
    (Batch d m × Remaining F) ≃ (Fin F.hardware.w × Fin F.hardware.r) where
  toFun | (batch,w,a) => (w,F.reservoirSplit.symm (batch,a))
  invFun | (w,r) => ((F.reservoirSplit r).1,w,(F.reservoirSplit r).2)
  left_inv z := by rcases z with ⟨batch,w,a⟩; simp
  right_inv z := by rcases z with ⟨w,r⟩; simp

def controllerView (F : Formation β τ q m) :
    (Batch d m × Rest F) ≃ Fin F.hardware.c × (Batch d m × Remaining F) where
  toFun | (batch,c,w,a) => (c,batch,w,a)
  invFun | (c,batch,w,a) => (batch,c,w,a)
  left_inv _ := rfl
  right_inv _ := rfl

def pairView (F : Formation β τ q m) :
    (Batch d m × Rest F) ≃ (Batch d m × Fin F.hardware.c) × Remaining F where
  toFun | (batch,c,w,a) => ((batch,c),w,a)
  invFun | ((batch,c),w,a) => (batch,c,w,a)
  left_inv _ := rfl
  right_inv _ := rfl

theorem body_product (F : Formation β τ q m)
    {z : ℕ} (t : Tester F.schedule z)
    (σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin z)))
    (h : FactoryControllerReturn.wholeState F.hardware t=F.hardware.controller.matrix ⊗ₖ σ.matrix) :
    (bodyOutput F.hardware.extension t).submatrix F.hardware.split.symm F.hardware.split.symm =
      F.hardware.controller.matrix ⊗ₖ partialRight σ.matrix := by
  ext ⟨c,wr⟩ ⟨c',wr'⟩
  change (∑ o,(finalState F.hardware.extension t)
    (F.hardware.split.symm (c,wr),o) (F.hardware.split.symm (c',wr'),o)) = _
  simp only [kroneckerMap_apply,partialRight,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  exact congrFun (congrFun h (c,wr,o)) (c',wr',o)

theorem result_product (F : Formation β τ q m)
    (σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)))
    (h : FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=
      F.hardware.controller.matrix ⊗ₖ σ.matrix) :
    ∃ ω : Density (Batch d m × Remaining F),
      result F=(F.hardware.controller.matrix ⊗ₖ ω.matrix).submatrix (controllerView F) (controllerView F) := by
  let ω : Density (Batch d m × Remaining F) :=
    ⟨(partialRight σ.matrix).submatrix (restFrame F) (restFrame F),
      (partialRight_positive σ.positive).submatrix _,by
        rw [submatrix_trace_equiv,partialRight_trace,σ.normalized]⟩
  refine ⟨ω,?_⟩
  have hb := body_product F (idleTester F.schedule) σ h
  ext ⟨batch,c,w,a⟩ ⟨batch',c',w',a'⟩
  have hh := congrFun (congrFun hb (c,w,F.reservoirSplit.symm (batch,a)))
    (c',w',F.reservoirSplit.symm (batch',a'))
  simpa only [result,coordinates,controllerView,restFrame,ω,submatrix_apply,
    Equiv.coe_fn_symm_mk,Equiv.coe_fn_mk,kroneckerMap_apply] using hh

theorem product_output (F : Formation β τ q m) (ω : Density (Batch d m × Remaining F))
    (h : result F=(F.hardware.controller.matrix ⊗ₖ ω.matrix).submatrix (controllerView F) (controllerView F)) :
    F.output=partialRight ω.matrix := by
  rw [← CacheFactoryBody.output,h]
  ext batch batch'
  simp only [partialRight,submatrix_apply,controllerView,Equiv.coe_fn_mk,
    kroneckerMap_apply,Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  have ht : ∑ c,F.hardware.controller.matrix c c=1 := F.hardware.controller.normalized
  rw [ht,one_mul]

theorem pair_product (F : Formation β τ q m) (ω : Density (Batch d m × Remaining F))
    (h : result F=(F.hardware.controller.matrix ⊗ₖ ω.matrix).submatrix (controllerView F) (controllerView F)) :
    partialRight ((result F).submatrix (pairView F).symm (pairView F).symm)=
      F.output ⊗ₖ F.hardware.controller.matrix := by
  rw [product_output F ω h,h]
  ext ⟨batch,c⟩ ⟨batch',c'⟩
  simp only [partialRight,submatrix_apply,pairView,controllerView,
    Equiv.coe_fn_symm_mk,Equiv.coe_fn_mk,kroneckerMap_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end ScheduleLaw.Blueprint.FactoryCacheMarginal
