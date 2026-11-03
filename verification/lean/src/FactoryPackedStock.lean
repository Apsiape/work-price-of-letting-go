import FactoryPacking

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPackedStock
open History FactoryPacking

def basis {a : Type} [DecidableEq a] (j : a) : Mat a :=
  pureMatrix (fun k => if k=j then 1 else 0)

theorem basis_diagonal {a : Type} [DecidableEq a] (j : a) :
    basis j=diagonal (fun k => if k=j then 1 else 0) := by
  ext i k
  by_cases hi : i=j <;> by_cases hk : k=j <;>
    simp_all [basis,pureMatrix,Matrix.diagonal,eq_comm]

theorem basis_product {a b : Type} [DecidableEq a] [DecidableEq b] (i : a) (k : b) :
    basis (i,k)=basis i ⊗ₖ basis k := by
  rw [basis_diagonal,basis_diagonal,basis_diagonal,diagonal_kronecker_diagonal]
  congr 1
  funext ⟨x,y⟩
  by_cases hx : x=i <;> by_cases hy : y=k <;> simp [hx,hy]

theorem work_zero : (basis initial).submatrix workEquiv workEquiv =
    SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ SupportRun.level 0)) := by
  have he : (basis initial).submatrix workEquiv workEquiv=
      basis ((0,0,0,0) : FactoryWorkFlags.Work) := by
    rw [basis_diagonal,basis_diagonal,submatrix_diagonal_equiv]
    congr 1
    funext w
    simp only [Function.comp_apply,initial,workEquiv.injective.eq_iff]
  rw [he,basis_product,basis_product,basis_product]
  rfl

def gibbsDensity {r : ℕ} (hr : 0<r) (β : ℝ) (H : Hamiltonian (Fin r)) : Density (Fin r) := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  exact ⟨gibbs β H,gibbs_positive β H,gibbs_trace β H⟩

/-- The literal Formation Gibbs initializer is exactly the checked
ten-register product, including every bath and the fresh reset stock. -/
theorem initialized_registers {d D r1 r2 r4 : ℕ} (hD : 0<D)
    (hr1 : 0<r1) (hr2 : 0<r2) (hr4 : 0<r4) (β : ℝ) (hβ : β≠0)
    (q : Density (Fin d)) (hq : q.matrix.PosDef) (m : ℕ)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4)) :
    ((FactoryFormation.flat D hD).matrix ⊗ₖ (basis initial ⊗ₖ
      gibbs β (FactoryFormation.reservoir (m:=m) β q (auxHamiltonian (D:=D) H1 H2 H4)))).submatrix
        (frame d m D r1 r2 r4) (frame d m D r1 r2 r4) =
      FactoryInitializer.matrix (FactoryFormation.flat D hD)
        (W2.tensorFamilyDensity (fun _ : Fin m => q))
        (gibbsDensity hr1 β H1) (gibbsDensity hr2 β H2) (gibbsDensity hr4 β H4)
        (FactoryFormation.flat D hD) := by
  rw [reservoir_stock hD β hβ q hq m H1 H2 H4]
  ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
  have hw := congrArg (fun A : Mat FactoryWorkFlags.Work =>
    A (w1,w2,w3,w4) (v1,v2,v3,v4)) work_zero
  simp only [submatrix_apply,kroneckerMap_apply] at hw
  simp only [frame,gather,Equiv.coe_fn_mk,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,
    Equiv.refl_apply,submatrix_apply,kroneckerMap_apply,Equiv.apply_symm_apply,
    Equiv.symm_apply_apply,FactoryInitializer.matrix,gibbsDensity,
    W2.tensorFamilyDensity,W2.tensorFamily,tensorPower]
  rw [hw]
  ring

end ScheduleLaw.Blueprint.FactoryPackedStock
