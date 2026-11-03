import PhaseHardwareReadouts
import PhaseProductReindex
import PhaseReturnStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseHardwareReturn
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def frame {b c r e : Type} (s : b ≃ c × r) : b × e ≃ c × (r × e) :=
  (Equiv.prodCongr s (Equiv.refl e)).trans (Equiv.prodAssoc c r e)

def oldShape (p : Driven S β) (z : ℕ) (X : Mat (Global p.extension z)) :
    Mat (Fin p.c × ((Fin p.w × Fin p.r) × (Payload I × Fin z))) :=
  X.submatrix (frame p.split).symm (frame p.split).symm

def newShape (p : Driven S β) (D z : ℕ) (X : Mat (Fin (p.extension.b*D) × (Payload I × Fin z))) :
    Mat (Fin (p.c*D) × ((Fin p.w × Fin p.r) × (Payload I × Fin z))) :=
  X.submatrix (frame (PhaseHardware.split p D)).symm (frame (PhaseHardware.split p D)).symm

theorem tensor_shape (p : Driven S β) {D z : ℕ} (φ : Density (Fin D)) (X : Mat (Global p.extension z)) :
    (newShape p D z ((X ⊗ₖ φ.matrix).submatrix (IdleExtension.wires p.extension.b D _)
      (IdleExtension.wires p.extension.b D _))).submatrix
      (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)) (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))=
        PhaseReturnTensor.state φ (oldShape p z X) := by
  ext ⟨⟨c,k⟩,wr,env⟩ ⟨⟨c',k'⟩,wr',env'⟩
  simp only [newShape,oldShape,frame,submatrix_apply,Equiv.symm_trans_apply,
    Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.prodAssoc_symm_apply,Prod.map_apply,
    Equiv.refl_apply,PhaseHardwareReadouts.split_inverse,IdleExtension.wires,Equiv.coe_fn_mk,
    Equiv.symm_apply_apply,PhaseReturnTensor.state,PhaseReturnTensor.frame,kroneckerMap_apply]
  ring

theorem controller_unpack (p : Driven S β) {D : ℕ} (φ : Density (Fin D)) :
    (PhaseHardware.controller p φ).matrix.submatrix finProdFinEquiv finProdFinEquiv=
      p.controller.matrix ⊗ₖ φ.matrix := by
  ext i j
  simp only [PhaseHardware.controller,submatrix_apply,Equiv.symm_apply_apply]

theorem idle_return (p : Driven S β) {D z : ℕ} (φ : Density (Fin D)) (X : Mat (Global p.extension z)) :
    let Y := newShape p D z ((X ⊗ₖ φ.matrix).submatrix (IdleExtension.wires p.extension.b D _)
      (IdleExtension.wires p.extension.b D _))
    traceDistance Y ((PhaseHardware.controller p φ).matrix ⊗ₖ partialLeft Y)=
      traceDistance (oldShape p z X) (p.controller.matrix ⊗ₖ partialLeft (oldShape p z X)) := by
  dsimp only
  have h := PhaseProductReindex.product_distance
    (finProdFinEquiv : Fin p.c × Fin D ≃ Fin (p.c*D)) (PhaseHardware.controller p φ)
    (newShape p D z ((X ⊗ₖ φ.matrix).submatrix (IdleExtension.wires p.extension.b D _)
      (IdleExtension.wires p.extension.b D _)))
  rw [tensor_shape,controller_unpack,PhaseReturnTensor.whole_rest] at h
  exact h.symm

theorem stability (p : Driven S β) {D z : ℕ} (φ : Density (Fin D)) (X : Mat (Global p.extension z))
    (Y : Mat (Fin (p.extension.b*D) × (Payload I × Fin z))) (η δ : ℝ)
    (hX : traceDistance (oldShape p z X) (p.controller.matrix ⊗ₖ partialLeft (oldShape p z X))≤η)
    (hY : traceDistance Y ((X ⊗ₖ φ.matrix).submatrix (IdleExtension.wires p.extension.b D _)
      (IdleExtension.wires p.extension.b D _))≤δ) :
    traceDistance (newShape p D z Y)
      ((PhaseHardware.controller p φ).matrix ⊗ₖ partialLeft (newShape p D z Y))≤η+2*δ := by
  apply PhaseReturnStability.whole_rest (PhaseHardware.controller p φ) (newShape p D z Y)
    (newShape p D z ((X ⊗ₖ φ.matrix).submatrix (IdleExtension.wires p.extension.b D _)
      (IdleExtension.wires p.extension.b D _))) δ η
  · unfold newShape
    rw [TraceMarginal.reindex_distance]
    exact hY
  · rw [idle_return]
    exact hX

end ScheduleLaw.Blueprint.PhaseHardwareReturn
