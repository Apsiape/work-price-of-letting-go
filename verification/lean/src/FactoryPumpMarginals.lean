import FactoryPhysicalPump

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPumpMarginals
open History FactoryRegisters FactoryRegisterOutput

def compose {a u v k l : Type} (E : a ≃ u × v) (F : u ≃ k × l) : a ≃ k × (l × v) :=
  E.trans ((Equiv.prodCongr F (Equiv.refl v)).trans (Equiv.prodAssoc k l v))

theorem marginal_compose {a u v k l : Type} [Fintype v] [Fintype l]
    (E : a ≃ u × v) (F : u ≃ k × l) (ρ : Mat a) :
    marginal (compose E F) ρ=marginal F (marginal E ρ) := by
  ext i j
  simp only [marginal,partialRight,compose,submatrix_apply,Equiv.symm_trans_apply,
    Equiv.prodAssoc_symm_apply,Equiv.prodCongr_symm,Equiv.prodCongr_apply,
    Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply,Fintype.sum_prod_type]

variable {b c e t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype e] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq e]
  [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

abbrev PumpRest := Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c

def codeLocal : ((b × (e × b)) × Fin 2) ≃ b × ((e × b) × Fin 2) :=
  Equiv.prodAssoc b (e × b) (Fin 2)

def batchLocal : ((b × (e × b)) × Fin 2) ≃ b × ((b × e) × Fin 2) :=
  (Equiv.prodCongr FactoryMarginals.lastFrame (Equiv.refl (Fin 2))).trans
    (Equiv.prodAssoc b (b × e) (Fin 2))

theorem codeLocal_marginal (ρ : Mat ((b × (e × b)) × Fin 2)) :
    marginal codeLocal ρ=partialRight (partialRight ρ) := by
  ext i j
  simp only [marginal,codeLocal,partialRight,submatrix_apply,Equiv.prodAssoc_symm_apply,
    Fintype.sum_prod_type]

theorem batchLocal_marginal (ρ : Mat ((b × (e × b)) × Fin 2)) :
    marginal batchLocal ρ=partialRight ((partialRight ρ).submatrix
      FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm) := by
  ext i j
  simp only [marginal,batchLocal,partialRight,submatrix_apply,Equiv.symm_trans_apply,
    Equiv.prodAssoc_symm_apply,Equiv.prodCongr_symm,Equiv.prodCongr_apply,
    Equiv.refl_symm,Equiv.refl_apply,Prod.map_apply,Fintype.sum_prod_type]

def codeRest : (e × (b × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c)) ≃
    ((e × b) × Fin 2) × PumpRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) where
  toFun
    | (res,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (((res,batch),w3),w1,w2,w4,bath1,bath2,bath4,fresh)
  invFun
    | (((res,batch),w3),w1,w2,w4,bath1,bath2,bath4,fresh) =>
      (res,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def batchRest (s : c ≃ b × e) : BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    ((b × e) × Fin 2) × PumpRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((s code,w3),w1,w2,w4,bath1,bath2,bath4,fresh)
  invFun
    | ((code,w3),w1,w2,w4,bath1,bath2,bath4,fresh) =>
      (s.symm code,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv z := by
    rcases z with ⟨code,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    simp only [Equiv.symm_apply_apply]
  right_inv z := by
    rcases z with ⟨⟨code,w3⟩,w1,w2,w4,bath1,bath2,bath4,fresh⟩
    simp only [Equiv.apply_symm_apply]

theorem code_marginal (s : c ≃ b × e)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    partialRight (partialRight (marginal (swapFrame s) ρ))=
      marginal (FactorySwapOutput.codingFrame s) ρ := by
  rw [← codeLocal_marginal,← marginal_compose]
  apply reframe (FactorySwapOutput.codingFrame s) (compose (swapFrame s) codeLocal) codeRest _ ρ
  intro z
  rfl

theorem batch_marginal (s : c ≃ b × e)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    partialRight ((partialRight (marginal (swapFrame s) ρ)).submatrix
      FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm)=marginal batchFrame ρ := by
  rw [← batchLocal_marginal,← marginal_compose]
  apply reframe batchFrame (compose (swapFrame s) batchLocal) (batchRest s) _ ρ
  intro z
  rfl

end ScheduleLaw.Blueprint.FactoryPumpMarginals


