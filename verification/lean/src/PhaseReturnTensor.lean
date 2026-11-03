import PhaseDensityTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseReturnTensor
variable {c p r : Type} [Fintype c] [Fintype p] [Fintype r]
  [DecidableEq c] [DecidableEq p] [DecidableEq r]

def frame : (c × p) × r ≃ p × (c × r) where
  toFun x := (x.1.2,(x.1.1,x.2))
  invFun x := ((x.2.1,x.1),x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def state (φ : Density p) (X : Mat (c × r)) : Mat ((c × p) × r) :=
  (φ.matrix ⊗ₖ X).submatrix frame frame

theorem rest (φ : Density p) (X : Mat (c × r)) : partialLeft (state φ X)=partialLeft X := by
  ext i j
  simp only [partialLeft,state,submatrix_apply,frame,Equiv.coe_fn_mk,kroneckerMap_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,← Finset.mul_sum]
  change (∑ z,φ.matrix z z)*(∑ z,X (z,i) (z,j))=_
  have hs : (∑ z,φ.matrix z z)=(1 : ℂ) := φ.normalized
  rw [hs,one_mul]

theorem product (φ : Density p) (ρ : Density c) (X : Mat (c × r)) :
    (ρ.matrix ⊗ₖ φ.matrix) ⊗ₖ partialLeft (state φ X)=
      state φ (ρ.matrix ⊗ₖ partialLeft X) := by
  rw [rest]
  ext i j
  simp only [state,submatrix_apply,frame,Equiv.coe_fn_mk,kroneckerMap_apply]
  ring

theorem whole_rest (φ : Density p) (ρ : Density c) (X : Mat (c × r)) :
    traceDistance (state φ X) ((ρ.matrix ⊗ₖ φ.matrix) ⊗ₖ partialLeft (state φ X))=
      traceDistance X (ρ.matrix ⊗ₖ partialLeft X) := by
  rw [product,state,state,TraceMarginal.reindex_distance,PhaseDensityTensor.distance]

end ScheduleLaw.Blueprint.PhaseReturnTensor
