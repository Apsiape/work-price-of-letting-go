import FactoryFourthSuccess

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPreparedSupport
open History FactoryRegisters FactoryRegisterOutput

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def secondRest : BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (c × (Fin 2 × t2)) × (Fin 2 × Fin 2 × Fin 2 × t1 × t4 × c) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((code,w2,bath2),w1,w3,w4,bath1,bath4,fresh)
  invFun
    | ((code,w2,bath2),w1,w3,w4,bath1,bath4,fresh) =>
      (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

theorem batch_after_second (U : Mat (c × (Fin 2 × t2))) (hU : IsUnitary U)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame (evolve (FactoryPlacement.place secondFrame U) ρ)=marginal batchFrame ρ := by
  let f := Equiv.refl (b × Fin 2 × Fin 2 × Fin 2 × t1 × t4 × c)
  let E := FactoryMarginals.outsideFrame (secondFrame (b:=b) (c:=c)
    (t1:=t1) (t2:=t2) (t4:=t4)) f
  have hr (σ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
      marginal E σ=marginal batchFrame σ :=
    reframe batchFrame E secondRest (by intro z; rfl) σ
  rw [← hr,← hr ρ]
  exact FactoryMarginals.disjoint_marginal secondFrame f U hU ρ

def decoderRest : (Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c ≃
    b × (Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c) where
  toFun
    | ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh) =>
      (batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  invFun
    | (batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh)
  left_inv _ := rfl
  right_inv _ := rfl

theorem batch_after_decoder (V : Mat c) (hV : IsUnitary V)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame (evolve (FactoryPlacement.place resetFrame V) ρ)=marginal batchFrame ρ :=
  FactoryMarginals.disjoint_marginal resetFrame decoderRest V hV ρ

def firstRest : BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (Fin 2 × t1) × (c × Fin 2 × Fin 2 × Fin 2 × t2 × t4 × c) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((w1,bath1),code,w2,w3,w4,bath2,bath4,fresh)
  invFun
    | ((w1,bath1),code,w2,w3,w4,bath2,bath4,fresh) =>
      (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

theorem batch_from_first
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame ρ=partialRight (marginal firstFrame ρ) := by
  let E := (firstFrame (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)).trans
    (Equiv.prodAssoc b (Fin 2 × t1) (c × Fin 2 × Fin 2 × Fin 2 × t2 × t4 × c))
  rw [← reframe batchFrame E firstRest (by intro z; rfl) ρ]
  ext i j
  simp only [marginal,partialRight,submatrix_apply,E,Equiv.symm_trans_apply,
    Equiv.prodAssoc_symm_apply,Fintype.sum_prod_type]

/-- The full swap/pump is an involution, including the third work bit. -/
theorem pump_twice {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    evolve (swapPump s) (evolve (swapPump s) ρ)=ρ := by
  rw [swapPump,FactoryPermutation.tensor,FactoryPermutation.place,
    Recorder.permutation_evolve,Recorder.permutation_evolve]
  ext i j
  simp only [submatrix_apply,FactoryPermutation.placed,Equiv.trans_apply,
    Equiv.apply_symm_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
    swapFrame,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,FactoryReset.swap,
    Fin.revPerm_apply,Fin.rev_rev,Equiv.apply_symm_apply,Prod.mk.eta,Equiv.symm_apply_apply]

theorem coding_after_swap {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal (FactorySwapOutput.codingFrame s) (evolve (swapPump s) ρ)=marginal batchFrame ρ := by
  have hh := FactorySwapOutput.batch_after_swap s (evolve (swapPump s) ρ)
  rw [pump_twice] at hh
  exact hh.symm

def fourthCodeRest : (Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c ≃
    (Fin 2 × t4) × (b × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × c) where
  toFun
    | ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh) =>
      ((w4,bath4),batch,w1,w2,w3,bath1,bath2,fresh)
  invFun
    | ((w4,bath4),batch,w1,w2,w3,bath1,bath2,fresh) =>
      ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh)
  left_inv _ := rfl
  right_inv _ := rfl

theorem code_from_fourth
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal resetFrame ρ=partialRight (marginal fourthFrame ρ) := by
  let E := (fourthFrame (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)).trans
    (Equiv.prodAssoc c (Fin 2 × t4) (b × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × c))
  rw [← reframe resetFrame E fourthCodeRest (by intro z; rfl) ρ]
  ext i j
  simp only [marginal,partialRight,submatrix_apply,E,Equiv.symm_trans_apply,
    Equiv.prodAssoc_symm_apply,Fintype.sum_prod_type]

theorem codeState_marginal {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c)
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) :
    (FactoryFourthSuccess.codeState s code batch γ1 γ2 fresh U1 U2 V h1 h2 hV).matrix=
      marginal resetFrame (evolve (FactoryFourthStock.before s U1 U2 V)
        (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)) := by
  rw [code_from_fourth,FactoryFourthStock.fourth_marginal,partialRight_kron]
  simp only [trace_kronecker,SupportRun.level_trace,γ4.normalized,one_mul,one_smul]
  rfl

/-- The extraction support includes the literal retained residue. Its actual
weight equals the prepared physical batch weight after the swap. -/
theorem support_weight {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c)
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (P : Mat b) :
    energy ((P ⊗ₖ (1 : Mat e)).submatrix s s)
      (FactoryFourthSuccess.codeState s code batch γ1 γ2 fresh U1 U2 V h1 h2 hV).matrix=
      energy P (partialRight (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix)))) := by
  rw [codeState_marginal s code batch γ1 γ2 γ4 fresh U1 U2 V h1 h2 hV]
  have he : ((P ⊗ₖ (1 : Mat e)).submatrix s s).submatrix s.symm s.symm=P ⊗ₖ (1 : Mat e) := by
    ext i j
    simp only [submatrix_apply,Equiv.apply_symm_apply]
  rw [← energy_reindex s.symm,he,energy_kron_one,← FactorySwapOutput.coding_marginal]
  rw [FactoryFourthStock.before,evolve_mul,evolve_mul,evolve_mul,coding_after_swap,
    batch_after_decoder V hV,batch_after_second U2 h2,batch_from_first]
  change energy P (partialRight
    (marginal firstFrame (evolve (FactoryPlacement.place firstFrame U1)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))))=_
  rw [show marginal firstFrame (evolve (FactoryPlacement.place firstFrame U1)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))=
      evolve U1 (marginal firstFrame (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)) from
        FactoryPlacement.operated_marginal firstFrame U1 _,FactoryInitializedFlags.first_stock]

end ScheduleLaw.Blueprint.FactoryPreparedSupport
