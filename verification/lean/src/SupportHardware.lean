import SupportFrameGeometry
import SupportBathReindex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportHardware
open History SupportPhysicalFrame

theorem frame_level {a c : Type} [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq c]
    (U : Fin 2 → Mat a) (A : Mat a) (B : Mat c) (k : Fin 2) :
    evolve (frame U) (A ⊗ₖ (SupportRun.level k ⊗ₖ B)) =
      evolve (U k) A ⊗ₖ (SupportRun.level k ⊗ₖ B) := by
  rw [← blocks_level,frame_evolve]
  have he : (fun j => evolve (U j) (if j=k then A else 0)) =
      (fun j => if j=k then evolve (U k) A else 0) := by
    funext j
    by_cases h : j=k
    · subst j; simp
    · simp [h,evolve]
  rw [he,blocks_level]

theorem diagonal_mask {a c : Type} [DecidableEq a] [DecidableEq c]
    (p : a → Prop) (q : c → Prop) [DecidablePred p] [DecidablePred q] (k : Fin 2) :
    diagonal (fun z : a × (Fin 2 × c) => if p z.1 ∧ z.2.1=k ∧ q z.2.2 then 1 else 0) =
      (diagonal (fun i => if p i then 1 else 0)) ⊗ₖ
        (SupportRun.level k ⊗ₖ (diagonal (fun j => if q j then 1 else 0))) := by
  rw [SupportRun.level_diagonal,diagonal_kronecker_diagonal,diagonal_kronecker_diagonal]
  congr 1
  funext z
  split_ifs <;> simp_all

theorem from_coordinates {d : ℕ} {c : Type} [Fintype c] [DecidableEq c] [Nonempty c]
    (β x f : ℝ) (H : Hamiltonian (Fin d)) (P Q UP UQ : Mat (Fin d))
    (EP EQ : Fin d → ℝ) (TP TQ : Finset (Fin d))
    (hUP : IsUnitary UP) (hUQ : IsUnitary UQ)
    (hHP : H.matrix=evolve UP (diagonal (fun i => (EP i : ℂ))))
    (hHQ : H.matrix=evolve UQ (diagonal (fun i => (EQ i : ℂ))))
    (hP : P=evolve UP (diagonal (fun i => if i∈TP then 1 else 0)))
    (hQ : Q=evolve UQ (diagonal (fun i => if i∈TQ then 1 else 0)))
    (R : c → ℝ) (G : Mat c) (U : Mat (Fin d × (Fin 2 × c)))
    (hU : IsUnitary U)
    (hcon : Conserves U (diagonal (fun z : Fin d × (Fin 2 × c) =>
      (((if z.2.1=0 then EP z.1 else EQ z.1+x)+R z.2.2 : ℝ) : ℂ))))
    (hgap : (Uᴴ*((diagonal (fun i => if i∈TQ then 1 else 0)) ⊗ₖ
      (SupportRun.level 1 ⊗ₖ (1 : Mat c)))*U -
        (diagonal (fun i => if i∈TP then 1 else 0)) ⊗ₖ (SupportRun.level 0 ⊗ₖ G)).PosSemidef)
    (hstock : 1-f ≤ energy G (gibbs β (FlatMatrix.diagonalHamiltonian c R))) :
    ∃ C : SupportConverter β H x, ∀ z (ρ : Density (Fin d × Fin z)),
      (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix →
      1-f ≤ energy ((Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  let V (w : Fin 2) := if w=0 then UP else UQ
  let W := frame (c:=c) V
  have hV (w : Fin 2) : IsUnitary (V w) := by
    dsimp [V]; split_ifs <;> assumption
  have hW : IsUnitary W := frame_unitary V hV
  have hs : evolve W ((diagonal (fun i => if i∈TQ then 1 else 0)) ⊗ₖ
      (SupportRun.level 1 ⊗ₖ (1 : Mat c))) = Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c)) := by
    rw [frame_level]
    simpa only [V,(by decide : (1 : Fin 2)≠0),if_false] using congrArg
      (fun A => A ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c))) hQ.symm
  have hi : evolve W ((diagonal (fun i => if i∈TP then 1 else 0)) ⊗ₖ
      (SupportRun.level 0 ⊗ₖ G)) = P ⊗ₖ (SupportRun.level 0 ⊗ₖ G) := by
    rw [frame_level]
    simpa only [V,if_true] using congrArg
      (fun A => A ⊗ₖ (SupportRun.level 0 ⊗ₖ G)) hP.symm
  let D : Mat (Fin d × (Fin 2 × c)) := diagonal (fun z =>
    (((if z.2.1=0 then EP z.1 else EQ z.1+x)+R z.2.2 : ℝ) : ℂ))
  have hHam : evolve W D = H.matrix ⊗ₖ (1 : Mat (Fin 2 × c)) +
      (1 : Mat (Fin d)) ⊗ₖ ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat c) +
        (1 : Mat (Fin 2)) ⊗ₖ (diagonal (fun k => (R k : ℂ)))) := by
    have h := frame_hamiltonian (c:=c) V hV H.matrix
      (fun w => if w=0 then EP else EQ) R (fun w => if w=0 then 0 else x)
      (by intro w; dsimp [V]; split_ifs
          · exact hHP.symm
          · exact hHQ.symm)
    have hd : diagonal (fun z : Fin d × (Fin 2 × c) =>
        (((if z.2.1=0 then EP else EQ) z.1+(if z.2.1=0 then 0 else x)+R z.2.2 : ℝ) : ℂ)) = D := by
      congr 1
      funext z
      by_cases hw : z.2.1=0 <;> simp [hw]
    have hx : (fun w : Fin 2 => ((if w=0 then 0 else x : ℝ) : ℂ)) = ![0,(x : ℂ)] := by
      funext w; fin_cases w <;> simp
    rw [hd,hx] at h
    exact h
  have hg := conjugate_effect W U _ _ hW hgap
  rw [hs,hi] at hg
  apply SupportBathReindex.physical_converter β x f H P Q R G (W*U*Wᴴ)
    (unitary_mul (unitary_mul hW hU) (FiniteFlat.adjoint_unitary hW)) _ hg hstock
  rw [← hHam]
  exact conjugate_conserves W U D hW hcon

end ScheduleLaw.Blueprint.SupportHardware
