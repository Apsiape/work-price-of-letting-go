import CacheFactoryBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheFactoryEnergy
open History CacheFactoryBody

variable {d m : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def helper (F : Formation β τ q m) : Mat (Rest F) :=
  F.hardware.HC.matrix ⊗ₖ (1 : Mat (Fin F.hardware.w × Fin F.aux)) +
    (1 : Mat (Fin F.hardware.c)) ⊗ₖ
      ((diagonal fun j => (F.hardware.batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin F.aux)) +
        (1 : Mat (Fin F.hardware.w)) ⊗ₖ F.auxiliaryHamiltonian.matrix)

def physical (F : Formation β τ q m) : Mat (Batch d m × Rest F) :=
  tensorHamiltonian (tangentHamiltonian β q) m ⊗ₖ (1 : Mat (Rest F)) +
    (1 : Mat (Batch d m)) ⊗ₖ helper F

theorem packed (F : Formation β τ q m) :
    F.hardware.bodyHamiltonian.submatrix (coordinates F).symm (coordinates F).symm=physical F := by
  ext ⟨u,c,w,a⟩ ⟨v,c',w',a'⟩
  have hs := congrFun (congrFun F.reservoirHamiltonian (u,a)) (v,a')
  simp only [submatrix_apply,Matrix.add_apply,kroneckerMap_apply] at hs
  have heq : F.reservoirSplit.symm (u,a)=F.reservoirSplit.symm (v,a') ↔ u=v ∧ a=a' := by
    rw [F.reservoirSplit.symm.injective.eq_iff]
    exact Prod.ext_iff
  simp only [Driven.bodyHamiltonian,submatrix_apply,coordinates,Equiv.coe_fn_symm_mk,
    Equiv.apply_symm_apply,Matrix.add_apply,kroneckerMap_apply,physical,helper]
  rw [hs]
  by_cases hu : u=v <;> by_cases hc : c=c' <;> by_cases hw : w=w' <;> by_cases ha : a=a' <;>
    simp [Matrix.one_apply,Prod.mk.injEq,heq,hu,hc,hw,ha] <;> ring

/-- The boundary ledger is the literal original Driven.defect, with the
complete factory bath/work/controller retained in the physical Hamiltonian. -/
theorem initialized_defect (F : Formation β τ q m) (hβ : β≠0) (hq : q.matrix.PosDef) :
    energy (physical F) (result F-tensorPower q.matrix m ⊗ₖ CacheFactoryBody.helper F) =
      Driven.defect F.hardware (idleTester F.schedule) := by
  rw [← packed F,← initialized F hβ hq]
  change energy (F.hardware.bodyHamiltonian.submatrix (coordinates F).symm (coordinates F).symm)
    ((bodyOutput F.hardware.extension (idleTester F.schedule)).submatrix
      (coordinates F).symm (coordinates F).symm -
      F.hardware.extension.source.matrix.submatrix (coordinates F).symm (coordinates F).symm)=_
  have hs : (bodyOutput F.hardware.extension (idleTester F.schedule)).submatrix
      (coordinates F).symm (coordinates F).symm -
      F.hardware.extension.source.matrix.submatrix (coordinates F).symm (coordinates F).symm =
      (bodyOutput F.hardware.extension (idleTester F.schedule)-F.hardware.extension.source.matrix).submatrix
        (coordinates F).symm (coordinates F).symm := by ext i j; rfl
  rw [hs,energy_reindex]
  simp only [Driven.defect,handoff_zero_visits F.hardware.extension F.empty,zero_add]

end ScheduleLaw.Blueprint.CacheFactoryEnergy
