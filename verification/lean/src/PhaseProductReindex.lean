import PhaseReturnTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseProductReindex
variable {a b r : Type} [Fintype a] [Fintype b] [Fintype r]
  [DecidableEq a] [DecidableEq b] [DecidableEq r]

theorem rest (e : a ≃ b) (X : Mat (b × r)) :
    partialLeft (X.submatrix (Equiv.prodCongr e (Equiv.refl r)) (Equiv.prodCongr e (Equiv.refl r)))=
      partialLeft X := by
  ext i j
  change (∑ x : a,X (e x,i) (e x,j))=∑ x : b,X (x,i) (x,j)
  exact Equiv.sum_comp e (fun x => X (x,i) (x,j))

theorem product_distance (e : a ≃ b) (ρ : Density b) (X : Mat (b × r)) :
    traceDistance (X.submatrix (Equiv.prodCongr e (Equiv.refl r)) (Equiv.prodCongr e (Equiv.refl r)))
      ((ρ.matrix.submatrix e e) ⊗ₖ partialLeft
        (X.submatrix (Equiv.prodCongr e (Equiv.refl r)) (Equiv.prodCongr e (Equiv.refl r))))=
      traceDistance X (ρ.matrix ⊗ₖ partialLeft X) := by
  rw [rest]
  have hp : (ρ.matrix.submatrix e e) ⊗ₖ partialLeft X=
      (ρ.matrix ⊗ₖ partialLeft X).submatrix (Equiv.prodCongr e (Equiv.refl r))
        (Equiv.prodCongr e (Equiv.refl r)) := by
    ext i j
    rfl
  rw [hp,TraceMarginal.reindex_distance]

end ScheduleLaw.Blueprint.PhaseProductReindex
