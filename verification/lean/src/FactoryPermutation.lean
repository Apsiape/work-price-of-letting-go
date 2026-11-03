import FactoryPlacement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPermutation
open History

theorem tensor {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (π : Equiv.Perm a) (σ : Equiv.Perm b) :
    π.permMatrix ℂ ⊗ₖ σ.permMatrix ℂ=Equiv.Perm.permMatrix ℂ (Equiv.prodCongr π σ) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [kroneckerMap_apply,Recorder.permutation_entry,Equiv.prodCongr_apply,
    Prod.map_apply,Prod.mk.injEq]
  by_cases hi : π i=j <;> by_cases hk : σ k=l <;> simp [hi,hk]

def placed {a b c : Type} (e : a ≃ b × c) (π : Equiv.Perm b) : Equiv.Perm a :=
  (e.trans (Equiv.prodCongr π (Equiv.refl c))).trans e.symm

theorem place {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] (e : a ≃ b × c) (π : Equiv.Perm b) :
    FactoryPlacement.place e (π.permMatrix ℂ)=(placed e π).permMatrix ℂ := by
  ext i j
  have he : placed e π i=j ↔ π (e i).1=(e j).1 ∧ (e i).2=(e j).2 := by
    rw [← e.injective.eq_iff]
    simp only [placed,Equiv.trans_apply,Equiv.apply_symm_apply]
    change (π (e i).1,(e i).2)=e j ↔ _
    exact Prod.ext_iff
  simp only [FactoryPlacement.place,submatrix_apply,kroneckerMap_apply,
    Recorder.permutation_entry,Matrix.one_apply,he]
  by_cases hi : π (e i).1=(e j).1 <;> by_cases hr : (e i).2=(e j).2 <;> simp [hi,hr]

end ScheduleLaw.Blueprint.FactoryPermutation
