import SupportRun
import FlatGibbs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportBathReindex
open History

theorem diagonal_gibbs_reindex {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (R : b → ℝ) (β : ℝ) :
    gibbs β (FlatMatrix.diagonalHamiltonian a (R ∘ e)) =
      (gibbs β (FlatMatrix.diagonalHamiltonian b R)).submatrix e e := by
  rw [FlatMatrix.diagonal_gibbs,FlatMatrix.diagonal_gibbs,submatrix_diagonal_equiv]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e (fun j => Real.exp (-β*R j))]

theorem physical_converter {d : ℕ} {c : Type} [Fintype c] [DecidableEq c] [Nonempty c]
    (β x f : ℝ) (H : Hamiltonian (Fin d)) (P Q : Mat (Fin d))
    (R : c → ℝ) (G : Mat c) (U : Mat (Fin d × (Fin 2 × c)))
    (hU : IsUnitary U)
    (hcon : Conserves U (H.matrix ⊗ₖ (1 : Mat (Fin 2 × c)) +
      (1 : Mat (Fin d)) ⊗ₖ ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat c) +
        (1 : Mat (Fin 2)) ⊗ₖ (diagonal (fun k => (R k : ℂ))))))
    (hgap : (Uᴴ*(Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c)))*U -
      P ⊗ₖ (SupportRun.level 0 ⊗ₖ G)).PosSemidef)
    (hstock : 1-f ≤ energy G (gibbs β (FlatMatrix.diagonalHamiltonian c R))) :
    ∃ C : SupportConverter β H x, ∀ z (ρ : Density (Fin d × Fin z)),
      (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix →
      1-f ≤ energy ((Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  let r := Fintype.card c
  let e : Fin r ≃ c := (Fintype.equivFin c).symm
  let J : (Fin d × (Fin 2 × Fin r)) ≃ (Fin d × (Fin 2 × c)) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) e)
  let HR := FlatMatrix.diagonalHamiltonian (Fin r) (R ∘ e)
  have hH : converterHamiltonian H HR x =
      (H.matrix ⊗ₖ (1 : Mat (Fin 2 × c)) + (1 : Mat (Fin d)) ⊗ₖ
        ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat c) +
          (1 : Mat (Fin 2)) ⊗ₖ (diagonal (fun k => (R k : ℂ))))).submatrix J J := by
    ext ⟨i,⟨w,k⟩⟩ ⟨j,⟨v,h⟩⟩
    simp [converterHamiltonian,HR,FlatMatrix.diagonalHamiltonian,J,
      Matrix.diagonal,Matrix.one_apply,e.injective.eq_iff]
  let C : SupportConverter β H x := {
    r := r
    r_pos := Fintype.card_pos
    HR := HR
    U := U.submatrix J J
    unitary := unitary_submatrix J hU
    conserves := by rw [hH]; exact conserves_reindex J U _ hcon }
  let Gf := G.submatrix e e
  have hsuc : (Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c))).submatrix J J =
      Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin r))) := by
    ext ⟨i,⟨w,k⟩⟩ ⟨j,⟨v,h⟩⟩
    simp [J,Matrix.one_apply,e.injective.eq_iff]
  have hinit : (P ⊗ₖ (SupportRun.level 0 ⊗ₖ G)).submatrix J J =
      P ⊗ₖ (SupportRun.level 0 ⊗ₖ Gf) := rfl
  have hgfin : (C.Uᴴ*(Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U -
      P ⊗ₖ (SupportRun.level 0 ⊗ₖ Gf)).PosSemidef := by
    have h := hgap.submatrix J
    simp only [submatrix_sub,Pi.sub_apply] at h
    rw [← submatrix_mul_equiv _ _ J J J,← submatrix_mul_equiv _ _ J J J,hsuc,hinit] at h
    simpa only [C,conjTranspose_submatrix] using h
  have hp : energy Gf (gibbs β C.HR) = energy G (gibbs β (FlatMatrix.diagonalHamiltonian c R)) := by
    change energy (G.submatrix e e) (gibbs β HR) = _
    rw [diagonal_gibbs_reindex,energy_reindex]
  refine ⟨C,fun z ρ hρ => ?_⟩
  have h := SupportRun.probability C P Q Gf hgfin z ρ hρ
  rw [hp] at h
  exact hstock.trans h

end ScheduleLaw.Blueprint.SupportBathReindex
