import FactoryTensorStock
import FactoryGibbsReindex
import FactoryReservoirEnergy

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheFactoryBody
open History

variable {d m : ℕ} {β : ℝ} {τ q : Density (Fin d)}

abbrev Batch (d m : ℕ) := Fin m → Fin d
abbrev Rest (F : Formation β τ q m) :=
  Fin F.hardware.c × (Fin F.hardware.w × Fin F.aux)

def coordinates (F : Formation β τ q m) :
    Fin F.hardware.extension.b ≃ Batch d m × Rest F where
  toFun i := let z := F.hardware.split i
             let r := F.reservoirSplit z.2.2
             (r.1,z.1,z.2.1,r.2)
  invFun | (batch,c,w,a) => F.hardware.split.symm (c,w,F.reservoirSplit.symm (batch,a))
  left_inv i := by simp only [Equiv.symm_apply_apply,Prod.mk.eta]
  right_inv i := by rcases i with ⟨batch,c,w,a⟩; simp only [Equiv.apply_symm_apply]

def unitary (F : Formation β τ q m) : Mat (Batch d m × Rest F) :=
  (emptyBodyMatrix F.inventory F.hardware.extension.b
    (F.hardware.extension.gate ⟨0,by omega⟩)).submatrix (coordinates F).symm (coordinates F).symm

def helper (F : Formation β τ q m) : Mat (Rest F) :=
  F.hardware.controller.matrix ⊗ₖ
    (pureMatrix (fun j => if j=F.hardware.initialLevel then 1 else 0) ⊗ₖ
      gibbs β F.auxiliaryHamiltonian)

def result (F : Formation β τ q m) : Mat (Batch d m × Rest F) :=
  (bodyOutput F.hardware.extension (idleTester F.schedule)).submatrix
    (coordinates F).symm (coordinates F).symm

theorem reservoir_stock (F : Formation β τ q m) (hβ : β≠0) (hq : q.matrix.PosDef) :
    (gibbs β F.hardware.HR).submatrix F.reservoirSplit.symm F.reservoirSplit.symm =
      tensorPower q.matrix m ⊗ₖ gibbs β F.auxiliaryHamiltonian := by
  have hh : FactoryGibbs.reindexHamiltonian F.reservoirSplit.symm F.hardware.HR =
      FactoryGibbs.sumHamiltonian
        (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) m) F.auxiliaryHamiltonian := by
    unfold FactoryGibbs.reindexHamiltonian FactoryGibbs.sumHamiltonian
    congr 1
    exact F.reservoirHamiltonian
  rw [← FactoryGibbs.gibbs_reindex,hh]
  exact FactoryTensor.batch_aux_stock β hβ q hq m F.auxiliaryHamiltonian

theorem initialized (F : Formation β τ q m) (hβ : β≠0) (hq : q.matrix.PosDef) :
    F.hardware.extension.source.matrix.submatrix (coordinates F).symm (coordinates F).symm =
      tensorPower q.matrix m ⊗ₖ helper F := by
  rw [F.hardware.source_product]
  ext ⟨u,c,w,a⟩ ⟨v,c',w',a'⟩
  have hs := congrFun (congrFun (reservoir_stock F hβ hq) (u,a)) (v,a')
  simp only [submatrix_apply,kroneckerMap_apply] at hs
  simp only [submatrix_apply,coordinates,Equiv.coe_fn_symm_mk,
    Equiv.apply_symm_apply,kroneckerMap_apply,helper]
  rw [hs]
  ring

theorem unitary_ok (F : Formation β τ q m) : IsUnitary (unitary F) := by
  exact unitary_submatrix _ (emptyBodyMatrix_unitary _ _ _
    (by simpa only [held_zero_visits F.schedule F.empty] using
      F.hardware.extension.gate_local ⟨0,by omega⟩))

theorem run (F : Formation β τ q m) (hβ : β≠0) (hq : q.matrix.PosDef) :
    evolve (unitary F) (tensorPower q.matrix m ⊗ₖ helper F) = result F := by
  rw [← initialized F hβ hq]
  change evolve ((emptyBodyMatrix _ _ _).submatrix _ _)
    (F.hardware.extension.source.matrix.submatrix _ _) = _
  rw [evolve_submatrix_equiv]
  rw [result,bodyOutput_zero_visits F.hardware.extension F.empty]
  rfl

theorem output (F : Formation β τ q m) : partialRight (result F)=F.output := by
  ext u v
  simp only [result,Formation.output,Driven.reservoirFinal,Driven.batteryReservoirFinal,
    partialRight,partialLeft,submatrix_apply,coordinates,Equiv.coe_fn_symm_mk,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext w
    rw [Finset.sum_comm]
  exact Finset.sum_comm

end ScheduleLaw.Blueprint.CacheFactoryBody
