import PhasePureTensor

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseDensityTensor
open History PhaseVectorDistance
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def frame : (a × b) × a ≃ (a × a) × b where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Adding an arbitrary normalized controller state does not magnify a
trace-norm error on the retained rest. -/
theorem trace_norm_le (ρ : Density a) (A : Mat b) :
    Matrix.traceNorm (ρ.matrix ⊗ₖ A)≤Matrix.traceNorm A := by
  let ψ := ρ.toMState.purify
  let v := ψ.vec
  have hv : ‖vector v‖=1 := by
    have hs := EuclideanSpace.norm_sq_eq (vector v)
    have hn : (∑ x,‖v x‖^2)=1 := ψ.normalized'
    simp only [vector,PiLp.toLp_apply] at hs
    rw [hn] at hs
    nlinarith [norm_nonneg (vector v)]
  have hρ : partialRight (pureMatrix v)=ρ.matrix := density_purification_matrix ρ.toMState
  have he : ρ.matrix ⊗ₖ A=
      partialRight ((pureMatrix v ⊗ₖ A).submatrix (frame (a:=a) (b:=b)) (frame (a:=a) (b:=b))) := by
    ext ⟨c,i⟩ ⟨d,j⟩
    have hh := congrFun (congrFun hρ c) d
    simp only [partialRight,pureMatrix] at hh
    simp only [partialRight,submatrix_apply,frame,Equiv.coe_fn_mk,kroneckerMap_apply,pureMatrix]
    rw [← hh,Finset.sum_mul]
  rw [he]
  calc _ ≤ Matrix.traceNorm ((pureMatrix v ⊗ₖ A).submatrix (frame (a:=a) (b:=b)) (frame (a:=a) (b:=b))) :=
           TraceMarginal.right_norm _
       _ = Matrix.traceNorm (pureMatrix v ⊗ₖ A) := TraceMarginal.reindex_norm _ _
       _ = Matrix.traceNorm A := PhasePureTensor.trace_norm v hv A

theorem distance_le (ρ : Density a) (X Y : Mat b) :
    traceDistance (ρ.matrix ⊗ₖ X) (ρ.matrix ⊗ₖ Y)≤traceDistance X Y := by
  unfold traceDistance
  rw [← CacheRareProduct.kron_sub,ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library]
  exact div_le_div_of_nonneg_right (trace_norm_le ρ (X-Y)) (by norm_num)

theorem distance (ρ : Density a) (X Y : Mat b) :
    traceDistance (ρ.matrix ⊗ₖ X) (ρ.matrix ⊗ₖ Y)=traceDistance X Y := by
  apply le_antisymm (distance_le ρ X Y)
  have h := TraceMarginal.left_distance (ρ.matrix ⊗ₖ X) (ρ.matrix ⊗ₖ Y)
  simpa only [partialLeft_kron,ρ.normalized,one_smul] using h

end ScheduleLaw.Blueprint.PhaseDensityTensor
