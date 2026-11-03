import FactoryRegisterOutput
import FactoryPermutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactorySwapOutput
open History FactoryRegisters FactoryRegisterOutput

variable {b c r t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype r] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq r]
  [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def codingFrame (e : c ≃ b × r) :
    R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
      b × (r × (b × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c)) where
  toFun z := ((e z.1).1,(e z.1).2,z.2)
  invFun z := (e.symm (z.1,z.2.1),z.2.2)
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by simp only [Equiv.apply_symm_apply,Prod.mk.eta]

def swapRest (e : c ≃ b × r) : BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    r × (b × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((e code).2,(e code).1,w1,w2,Fin.rev w3,w4,bath1,bath2,bath4,fresh)
  invFun
    | (res,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (e.symm (batch,res),w1,w2,Fin.rev w3,w4,bath1,bath2,bath4,fresh)
  left_inv z := by
    rcases z with ⟨code,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    simp only [Prod.mk.eta,Equiv.symm_apply_apply,Fin.rev_rev]
  right_inv z := by
    rcases z with ⟨res,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    simp only [Equiv.apply_symm_apply,Fin.rev_rev]

/-- The actual placed swap/pump, including its third work bit and all retired
stocks, emits the pre-swap coding batch for every matrix. -/
theorem batch_after_swap (e : c ≃ b × r)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame (evolve (swapPump e) ρ)=marginal (codingFrame e) ρ := by
  rw [swapPump,FactoryPermutation.tensor,FactoryPermutation.place,Recorder.permutation_evolve]
  ext i j
  exact Equiv.sum_comp (swapRest e)
    (fun k => ρ ((codingFrame e).symm (i,k)) ((codingFrame e).symm (j,k)))

omit [DecidableEq b] [DecidableEq c] [DecidableEq r]
  [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem coding_marginal (e : c ≃ b × r)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal (codingFrame e) ρ=
      partialRight ((marginal resetFrame ρ).submatrix e.symm e.symm) := by
  ext i j
  simp only [marginal,codingFrame,partialRight,submatrix_apply,Equiv.coe_fn_symm_mk,
    Fintype.sum_prod_type]
  rfl

/-- Output identity for the literal complete four-register circuit. Extraction
and final reset preserve the unconditional emitted batch, including all failed
converter columns and all correlations. -/
theorem circuit_batch (e : c ≃ b × r)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4))) (h4 : IsUnitary U4)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame (evolve (circuit e U1 U2 V U4) ρ) =
      partialRight ((evolve V (marginal resetFrame
        (evolve (FactoryPlacement.place secondFrame U2)
          (evolve (FactoryPlacement.place firstFrame U1) ρ)))).submatrix e.symm e.symm) := by
  simp only [circuit,evolve_mul]
  rw [batch_after_reset,batch_after_fourth U4 h4,batch_after_swap,coding_marginal]
  rw [show marginal resetFrame
    (evolve (FactoryPlacement.place resetFrame V)
      (evolve (FactoryPlacement.place secondFrame U2)
        (evolve (FactoryPlacement.place firstFrame U1) ρ))) =
    evolve V (marginal resetFrame
      (evolve (FactoryPlacement.place secondFrame U2)
        (evolve (FactoryPlacement.place firstFrame U1) ρ))) from
      FactoryPlacement.operated_marginal resetFrame V _]

end ScheduleLaw.Blueprint.FactorySwapOutput
