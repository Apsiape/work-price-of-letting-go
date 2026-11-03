import PhaseHardware

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseHardwareReadouts
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

theorem split_inverse (p : Driven S β) (D : ℕ) (c : Fin p.c) (z : Fin D)
    (wr : Fin p.w × Fin p.r) :
    (PhaseHardware.split p D).symm (finProdFinEquiv (c,z),wr)=
      finProdFinEquiv (p.split.symm (c,wr),z) := by
  apply (PhaseHardware.split p D).injective
  simp only [Equiv.apply_symm_apply,PhaseHardware.split_apply,Equiv.symm_apply_apply]

def whole (p : Driven S β) {D : ℕ} (M : Mat (Fin p.extension.b)) (φ : Mat (Fin D)) :
    Mat (Fin (p.c*D) × (Fin p.w × Fin p.r)) :=
  ((M ⊗ₖ φ).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
    (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm

theorem controller (p : Driven S β) {D : ℕ} (M : Mat (Fin p.extension.b)) (φ : Mat (Fin D)) :
    partialRight (whole p M φ)=
      ((partialRight (M.submatrix p.split.symm p.split.symm)) ⊗ₖ φ).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  obtain ⟨⟨c,z⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨c',z'⟩,rfl⟩ := finProdFinEquiv.surjective j
  simp only [partialRight,whole,submatrix_apply,split_inverse,Equiv.symm_apply_apply,kroneckerMap_apply]
  change (∑ x : Fin p.w × Fin p.r,M (p.split.symm (c,x)) (p.split.symm (c',x))*φ z z')=
    (∑ x : Fin p.w × Fin p.r,M (p.split.symm (c,x)) (p.split.symm (c',x)))*φ z z'
  exact (Finset.sum_mul Finset.univ (fun x : Fin p.w × Fin p.r =>
    M (p.split.symm (c,x)) (p.split.symm (c',x))) (φ z z')).symm

theorem rest (p : Driven S β) {D : ℕ} (M : Mat (Fin p.extension.b)) (φ : Density (Fin D)) :
    partialLeft (whole p M φ.matrix)=partialLeft (M.submatrix p.split.symm p.split.symm) := by
  have ht : (∑ z,φ.matrix z z)=(1 : ℂ) := φ.normalized
  ext i j
  change (∑ c : Fin (p.c*D),whole p M φ.matrix (c,i) (c,j))=_
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin p.c × Fin D ≃ Fin (p.c*D))]
  simp only [Fintype.sum_prod_type,whole,submatrix_apply,split_inverse,Equiv.symm_apply_apply,kroneckerMap_apply]
  change (∑ c : Fin p.c,∑ z : Fin D,M (p.split.symm (c,i)) (p.split.symm (c,j))*φ.matrix z z)=
    ∑ c : Fin p.c,M (p.split.symm (c,i)) (p.split.symm (c,j))
  simp only [← Finset.mul_sum,ht,mul_one]

end ScheduleLaw.Blueprint.PhaseHardwareReadouts
