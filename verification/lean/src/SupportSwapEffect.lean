import FiniteSwap
import SupportEffect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportSwapEffect

/-- The full swap's pulled-back success effect dominates every initialized
 good source column. This is an operator inequality, including coherences. -/
theorem conserving_swap_effect {a o : Type} [Fintype o] [DecidableEq o]
    (s t : a → o) (hs : Function.Injective s) (ht : Function.Injective t)
    (hd : ∀ i j,s i ≠ t j) (E : o → ℝ) (he : ∀ i,E (t i)=E (s i))
    (q : o → Prop) (hq : ∀ i,q (t i)) :
    ∃ U : Mat o, IsUnitary U ∧ Conserves U (diagonal (fun i => (E i : ℂ))) ∧
      (Uᴴ*diagonal (fun i => if q i then 1 else 0)*U -
        diagonal (fun j => if ∃ i,s i=j then 1 else 0)).PosSemidef := by
  let π := FiniteSwap.permutation s t hs ht hd
  let U : Mat o := π.permMatrix ℂ
  have hstar : Uᴴ=U := by
    change (π.permMatrix ℂ)ᴴ=π.permMatrix ℂ
    rw [conjTranspose_permMatrix]
    rfl
  refine ⟨U,FiniteSwap.unitary s t hs ht hd,FiniteSwap.conserves s t hs ht hd E he,?_⟩
  have hev : Uᴴ*diagonal (fun i => if q i then 1 else 0)*U =
      evolve U (diagonal (fun i => if q i then 1 else 0)) := by
    simp only [evolve,hstar]
  rw [hev,FiniteSwap.diagonal_evolution s t hs ht hd,diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases hj : ∃ i,s i=j
  · obtain ⟨i,rfl⟩ := hj
    have hp : π (s i)=t i := FiniteSwap.on_source s t hs i
    have hex : ∃ k,s k=s i := ⟨i,rfl⟩
    simp only [if_pos hex]
    rw [show FiniteSwap.permutation s t hs ht hd (s i)=t i from hp,if_pos (hq i)]
    simp
  · simp only [if_neg hj,sub_zero]
    split_ifs <;> norm_num

/-- The same operator bound tensored with any coherent finite reference. -/
theorem reference_probability {o z : Type} [Fintype o] [DecidableEq o]
    [Fintype z] [DecidableEq z] (U Q P : Mat o)
    (hgap : (Uᴴ*Q*U-P).PosSemidef) (ρ : Density (o × z)) :
    energy (P ⊗ₖ (1 : Mat z)) ρ.matrix ≤
      energy ((Uᴴ*Q*U) ⊗ₖ (1 : Mat z)) ρ.matrix := by
  apply SupportEffect.energy_mono _ _ _ _ ρ.positive
  have he : ((Uᴴ*Q*U-P) ⊗ₖ (1 : Mat z)) =
      ((Uᴴ*Q*U) ⊗ₖ (1 : Mat z))-(P ⊗ₖ (1 : Mat z)) := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp only [kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [← he]
  exact hgap.kronecker (Matrix.PosSemidef.one : (1 : Mat z).PosSemidef)

end ScheduleLaw.Blueprint.SupportSwapEffect
