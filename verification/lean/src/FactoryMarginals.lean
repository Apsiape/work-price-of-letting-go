import FactoryRegisters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryMarginals
open History

variable {a b c s t : Type} [Fintype a] [Fintype b] [Fintype c]
  [Fintype s] [Fintype t] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  [DecidableEq s] [DecidableEq t]

def outsideFrame (e : a ≃ b × c) (f : c ≃ s × t) : a ≃ s × (b × t) where
  toFun z := ((f (e z).2).1,(e z).1,(f (e z).2).2)
  invFun z := e.symm (z.2.1,f.symm (z.1,z.2.2))
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by simp only [Equiv.apply_symm_apply,Prod.mk.eta]

omit [Fintype a] [Fintype c] [Fintype s]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq s] [DecidableEq t] in
theorem outside_marginal (e : a ≃ b × c) (f : c ≃ s × t) (ρ : Mat a) :
    partialRight (ρ.submatrix (outsideFrame e f).symm (outsideFrame e f).symm) =
      partialRight ((partialLeft (ρ.submatrix e.symm e.symm)).submatrix f.symm f.symm) := by
  ext i j
  simp only [partialRight,partialLeft,submatrix_apply,outsideFrame,
    Equiv.coe_fn_symm_mk,Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq s] [DecidableEq t] in
/-- A placed unitary leaves every subsystem of its complete rest unchanged,
including correlations with other retained registers. -/
theorem disjoint_marginal (e : a ≃ b × c) (f : c ≃ s × t) (U : Mat b)
    (hU : IsUnitary U) (ρ : Mat a) :
    partialRight ((evolve (FactoryPlacement.place e U) ρ).submatrix
      (outsideFrame e f).symm (outsideFrame e f).symm) =
      partialRight (ρ.submatrix (outsideFrame e f).symm (outsideFrame e f).symm) := by
  rw [outside_marginal,FactoryPlacement.rest_invariant e U hU,outside_marginal]

omit [Fintype a] [Fintype b] [Fintype c] [Fintype s] [Fintype t]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq s] [DecidableEq t] in
def lastFrame : (a × (b × a)) ≃ a × (a × b) where
  toFun z := (z.2.2,z.1,z.2.1)
  invFun z := (z.2.1,z.2.2,z.1)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype c] [Fintype s] [Fintype t] [DecidableEq c]
  [DecidableEq s] [DecidableEq t] in
theorem swapped_batch (ρ : Mat (a × (b × a))) :
    partialRight ((evolve ((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ρ).submatrix
      lastFrame.symm lastFrame.symm)=partialRight ρ := by
  rw [Recorder.permutation_evolve]
  ext i j
  simp only [partialRight,submatrix_apply,lastFrame,FactoryReset.swap,
    Equiv.coe_fn_symm_mk,Equiv.coe_fn_mk,Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype c] [Fintype s] [Fintype t] [DecidableEq c]
  [DecidableEq s] [DecidableEq t] in
theorem partialRight_evolve_product (U : Mat a) (V : Mat b) (hV : IsUnitary V)
    (ρ : Mat (a × b)) :
    partialRight (evolve (U ⊗ₖ V) ρ)=evolve U (partialRight ρ) := by
  have he : U ⊗ₖ V=(U ⊗ₖ (1 : Mat b))*((1 : Mat a) ⊗ₖ V) := by
    rw [← mul_kronecker_mul,mul_one,one_mul]
  rw [he,evolve_mul,partialRight_evolve_kron_one,partialRight_evolve_one_kron V _ hV]

omit [Fintype c] [Fintype s] [Fintype t] [DecidableEq c]
  [DecidableEq s] [DecidableEq t] in
/-- The swap/pump's emitted batch is the complete pre-swap coding batch.
The third work bit and all coding correlations are traced only after the
full square swap and work flip have acted. -/
theorem swap_pump_batch (ρ : Mat ((a × (b × a)) × Fin 2)) :
    partialRight ((partialRight (evolve
      (((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ⊗ₖ
        ((Fin.revPerm (n:=2)).permMatrix ℂ)) ρ)).submatrix
      lastFrame.symm lastFrame.symm)=partialRight (partialRight ρ) := by
  rw [partialRight_evolve_product _ _ (Recorder.permutation_unitary _),swapped_batch]

end ScheduleLaw.Blueprint.FactoryMarginals
