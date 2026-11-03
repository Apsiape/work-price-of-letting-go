import FactoryFreshFrame
import FactoryInitializer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFourthStock
open History FactoryRegisters FactoryRegisterOutput

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

abbrev Reference := b × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × c
abbrev Old := c × Reference (b:=b) (c:=c) (t1:=t1) (t2:=t2)

def frame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2)) × (Fin 2 × t4) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((code,batch,w1,w2,w3,bath1,bath2,fresh),w4,bath4)
  invFun
    | ((code,batch,w1,w2,w3,bath1,bath2,fresh),w4,bath4) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def first : Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) ≃
    (b × (Fin 2 × t1)) × (c × Fin 2 × Fin 2 × t2 × c) where
  toFun
    | (code,batch,w1,w2,w3,bath1,bath2,fresh) =>
      ((batch,w1,bath1),code,w2,w3,bath2,fresh)
  invFun
    | ((batch,w1,bath1),code,w2,w3,bath2,fresh) =>
      (code,batch,w1,w2,w3,bath1,bath2,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def second : Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) ≃
    (c × (Fin 2 × t2)) × (b × Fin 2 × Fin 2 × t1 × c) where
  toFun
    | (code,batch,w1,w2,w3,bath1,bath2,fresh) =>
      ((code,w2,bath2),batch,w1,w3,bath1,fresh)
  invFun
    | ((code,w2,bath2),batch,w1,w3,bath1,fresh) =>
      (code,batch,w1,w2,w3,bath1,bath2,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def pump {e : Type} (s : c ≃ b × e) : Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) ≃
    ((b × (e × b)) × Fin 2) × (Fin 2 × Fin 2 × t1 × t2 × c) where
  toFun
    | (code,batch,w1,w2,w3,bath1,bath2,fresh) =>
      ((((s code).1,(s code).2,batch),w3),w1,w2,bath1,bath2,fresh)
  invFun
    | (((cb,ce,batch),w3),w1,w2,bath1,bath2,fresh) =>
      (s.symm (cb,ce),batch,w1,w2,w3,bath1,bath2,fresh)
  left_inv z := by rcases z with ⟨code,batch,w1,w2,w3,bath1,bath2,fresh⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨⟨cb,ce,batch⟩,w3⟩,w1,w2,bath1,bath2,fresh⟩; simp only [Equiv.apply_symm_apply]

theorem first_factor (U : Mat (b × (Fin 2 × t1))) :
    FactoryPlacement.place firstFrame U =
      (FactoryPlacement.place (first (c:=c) (t2:=t2)) U ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame := by
  apply FactoryFreshFrame.factor_place
  · intro i; rfl
  · intro i j
    simp only [firstFrame,frame,first,Equiv.refl_apply,Equiv.coe_fn_mk,Prod.mk.injEq]
    tauto

theorem second_factor (U : Mat (c × (Fin 2 × t2))) :
    FactoryPlacement.place secondFrame U =
      (FactoryPlacement.place (second (b:=b) (t1:=t1)) U ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame := by
  apply FactoryFreshFrame.factor_place
  · intro i; rfl
  · intro i j
    simp only [secondFrame,frame,second,Equiv.refl_apply,Equiv.coe_fn_mk,Prod.mk.injEq]
    tauto

theorem decoder_factor (U : Mat (c)) :
    FactoryPlacement.place resetFrame U =
      (FactoryPlacement.place (Equiv.refl (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2))) U ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame := by
  apply FactoryFreshFrame.factor_place
  · intro i; rfl
  · intro i j
    simp only [resetFrame,frame,Equiv.refl_apply,Equiv.coe_fn_mk,Prod.mk.injEq]
    tauto

theorem pump_factor {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e) :
    swapPump (t1:=t1) (t2:=t2) (t4:=t4) s =
      (FactoryPlacement.place (pump (t1:=t1) (t2:=t2) s)
        ((FactoryReset.swap (a:=b) (b:=e)).permMatrix ℂ ⊗ₖ (Fin.revPerm (n:=2)).permMatrix ℂ) ⊗ₖ
          (1 : Mat (Fin 2 × t4))).submatrix frame frame := by
  unfold swapPump
  apply FactoryFreshFrame.factor_place
  · intro i; rfl
  · intro i j
    simp only [swapFrame,frame,pump,Equiv.coe_fn_mk,Prod.mk.injEq]
    tauto

def preprocess {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c) :
    Mat (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2)) :=
  FactoryPlacement.place (pump s)
    ((FactoryReset.swap (a:=b) (b:=e)).permMatrix ℂ ⊗ₖ (Fin.revPerm (n:=2)).permMatrix ℂ) *
    FactoryPlacement.place (Equiv.refl _) V * FactoryPlacement.place second U2 *
      FactoryPlacement.place first U1

def before {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c) :
    Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  swapPump s * FactoryPlacement.place resetFrame V * FactoryPlacement.place secondFrame U2 *
    FactoryPlacement.place firstFrame U1

theorem before_factor {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c) :
    before (t4:=t4) s U1 U2 V =
      (preprocess s U1 U2 V ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame := by
  have hm (A B : Mat (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2))) :
      ((A*B) ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame =
        (A ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame *
          (B ⊗ₖ (1 : Mat (Fin 2 × t4))).submatrix frame frame := by
    rw [FactoryFreshFrame.kron_one_mul]
    exact (submatrix_mul_equiv _ _ frame frame frame).symm
  rw [before,first_factor,second_factor,decoder_factor,pump_factor]
  simp only [preprocess,hm]

theorem preprocess_unitary {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c)
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) :
    IsUnitary (preprocess s U1 U2 V) := by
  exact unitary_mul (unitary_mul (unitary_mul
    (FactoryPlacement.unitary _ _ (unitary_kron FactoryReset.unitary (Recorder.permutation_unitary _)))
    (FactoryPlacement.unitary _ _ hV)) (FactoryPlacement.unitary _ _ h2))
    (FactoryPlacement.unitary _ _ h1)

def oldMatrix (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (fresh : Density c) : Mat (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2)) :=
  code.matrix ⊗ₖ (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ
    (SupportRun.level 0 ⊗ₖ (γ1.matrix ⊗ₖ (γ2.matrix ⊗ₖ fresh.matrix))))))

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem initial_factor (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh=
      (oldMatrix code batch γ1 γ2 fresh ⊗ₖ (SupportRun.level 0 ⊗ₖ γ4.matrix)).submatrix frame frame := by
  ext ⟨code0,batch0,w1,w2,w3,w4,bath1,bath2,bath4,fresh0⟩
    ⟨code1,batch1,v1,v2,v3,v4,bath1',bath2',bath4',fresh1⟩
  simp only [FactoryInitializer.matrix,oldMatrix,frame,Equiv.coe_fn_mk,submatrix_apply,kroneckerMap_apply]
  ring

/-- Until extraction, the fourth converter's work/bath stock is literally
untouched and independent, while all other registers may be correlated. -/
theorem before_output {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c) :
    evolve (before s U1 U2 V) (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)=
      (evolve (preprocess s U1 U2 V) (oldMatrix code batch γ1 γ2 fresh) ⊗ₖ
        (SupportRun.level 0 ⊗ₖ γ4.matrix)).submatrix frame frame := by
  rw [before_factor,initial_factor,evolve_submatrix_equiv]
  simp only [evolve,conjTranspose_kronecker,conjTranspose_one,← mul_kronecker_mul,
    one_mul,mul_one]

theorem fourth_marginal {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c) :
    marginal fourthFrame (evolve (before s U1 U2 V)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))=
      partialRight (evolve (preprocess s U1 U2 V) (oldMatrix code batch γ1 γ2 fresh)) ⊗ₖ
        (SupportRun.level 0 ⊗ₖ γ4.matrix) := by
  rw [before_output]
  ext ⟨i,w,u⟩ ⟨j,v,z⟩
  simp only [marginal,partialRight,submatrix_apply,fourthFrame,frame,Equiv.coe_fn_symm_mk,
    Equiv.coe_fn_mk,kroneckerMap_apply]
  exact (Finset.sum_mul _ _ _).symm

end ScheduleLaw.Blueprint.FactoryFourthStock
