import FactoryRegisters
import FactoryResetCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFreshFrame
open History FactoryRegisters

/-- A placed gate factors through an untouched last register. -/
theorem factor_place {a u v o f t : Type}
    [Fintype a] [Fintype u] [Fintype v] [Fintype o] [Fintype f] [Fintype t]
    [DecidableEq a] [DecidableEq u] [DecidableEq v]
    [DecidableEq o] [DecidableEq f] [DecidableEq t]
    (E : a ≃ u × t) (F : a ≃ o × f) (G : o ≃ u × v)
    (h1 : ∀ i, (E i).1=(G (F i).1).1)
    (h2 : ∀ i j, (E i).2=(E j).2 ↔
      (G (F i).1).2=(G (F j).1).2 ∧ (F i).2=(F j).2) (U : Mat u) :
    FactoryPlacement.place E U =
      (FactoryPlacement.place G U ⊗ₖ (1 : Mat f)).submatrix F F := by
  ext i j
  simp only [FactoryPlacement.place,submatrix_apply,kroneckerMap_apply,
    one_apply,h1,h2]
  split_ifs <;> simp_all

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

abbrev Old := c × Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)

def frame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) × c :=
  resetFrame.trans (Equiv.prodAssoc c (Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) c).symm

def first : Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (b × (Fin 2 × t1)) × (c × Fin 2 × Fin 2 × Fin 2 × t2 × t4) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4) =>
      ((batch,w1,bath1),code,w2,w3,w4,bath2,bath4)
  invFun
    | ((batch,w1,bath1),code,w2,w3,w4,bath2,bath4) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4)
  left_inv _ := rfl
  right_inv _ := rfl

def second : Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (c × (Fin 2 × t2)) × (b × Fin 2 × Fin 2 × Fin 2 × t1 × t4) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4) =>
      ((code,w2,bath2),batch,w1,w3,w4,bath1,bath4)
  invFun
    | ((code,w2,bath2),batch,w1,w3,w4,bath1,bath4) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4)
  left_inv _ := rfl
  right_inv _ := rfl

def fourth : Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (c × (Fin 2 × t4)) × (b × Fin 2 × Fin 2 × Fin 2 × t1 × t2) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4) =>
      ((code,w4,bath4),batch,w1,w2,w3,bath1,bath2)
  invFun
    | ((code,w4,bath4),batch,w1,w2,w3,bath1,bath2) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4)
  left_inv _ := rfl
  right_inv _ := rfl

def pump {e : Type} (s : c ≃ b × e) :
    Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
      ((b × (e × b)) × Fin 2) × (Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4) =>
      ((((s code).1,(s code).2,batch),w3),w1,w2,w4,bath1,bath2,bath4)
  invFun
    | (((cb,ce,batch),w3),w1,w2,w4,bath1,bath2,bath4) =>
      (s.symm (cb,ce),batch,w1,w2,w3,w4,bath1,bath2,bath4)
  left_inv z := by rcases z with ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨⟨cb,ce,batch⟩,w3⟩,w1,w2,w4,bath1,bath2,bath4⟩; simp only [Equiv.apply_symm_apply]

theorem first_factor (U : Mat (b × (Fin 2 × t1))) :
    FactoryPlacement.place firstFrame U =
      (FactoryPlacement.place (first (c:=c) (t2:=t2) (t4:=t4)) U ⊗ₖ (1 : Mat c)).submatrix frame frame := by
  apply factor_place
  · intro i; rfl
  · intro i j
    simp only [firstFrame,frame,resetFrame,first,Equiv.trans_apply,Equiv.coe_fn_mk,
      Equiv.prodAssoc_symm_apply,Prod.mk.injEq]
    tauto

theorem second_factor (U : Mat (c × (Fin 2 × t2))) :
    FactoryPlacement.place secondFrame U =
      (FactoryPlacement.place (second (b:=b) (t1:=t1) (t4:=t4)) U ⊗ₖ (1 : Mat c)).submatrix frame frame := by
  apply factor_place
  · intro i; rfl
  · intro i j
    simp only [secondFrame,frame,resetFrame,second,Equiv.trans_apply,Equiv.coe_fn_mk,
      Equiv.prodAssoc_symm_apply,Prod.mk.injEq]
    tauto

theorem fourth_factor (U : Mat (c × (Fin 2 × t4))) :
    FactoryPlacement.place fourthFrame U =
      (FactoryPlacement.place (fourth (b:=b) (t1:=t1) (t2:=t2)) U ⊗ₖ (1 : Mat c)).submatrix frame frame := by
  apply factor_place
  · intro i; rfl
  · intro i j
    simp only [fourthFrame,frame,resetFrame,fourth,Equiv.trans_apply,Equiv.coe_fn_mk,
      Equiv.prodAssoc_symm_apply,Prod.mk.injEq]
    tauto

theorem decoder_factor (V : Mat c) :
    FactoryPlacement.place resetFrame V =
      (FactoryPlacement.place (Equiv.refl (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) V ⊗ₖ
        (1 : Mat c)).submatrix frame frame := by
  apply factor_place
  · intro i; rfl
  · intro i j
    simp only [resetFrame,frame,Equiv.trans_apply,Equiv.coe_fn_mk,
      Equiv.prodAssoc_symm_apply,Equiv.refl_apply,Prod.mk.injEq]

theorem pump_factor {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e) :
    swapPump (t1:=t1) (t2:=t2) (t4:=t4) s =
      (FactoryPlacement.place (pump (t1:=t1) (t2:=t2) (t4:=t4) s)
        ((FactoryReset.swap (a:=b) (b:=e)).permMatrix ℂ ⊗ₖ
          (Fin.revPerm (n:=2)).permMatrix ℂ) ⊗ₖ (1 : Mat c)).submatrix frame frame := by
  unfold swapPump
  apply factor_place
  · intro i; rfl
  · intro i j
    simp only [swapFrame,frame,resetFrame,pump,Equiv.trans_apply,Equiv.coe_fn_mk,
      Equiv.prodAssoc_symm_apply,Prod.mk.injEq]
    tauto

def preprocess {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4))) :
    Mat (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  FactoryPlacement.place fourth U4 *
    FactoryPlacement.place (pump s)
      ((FactoryReset.swap (a:=b) (b:=e)).permMatrix ℂ ⊗ₖ (Fin.revPerm (n:=2)).permMatrix ℂ) *
    FactoryPlacement.place (Equiv.refl _) V * FactoryPlacement.place second U2 *
      FactoryPlacement.place first U1

theorem preprocess_unitary {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    IsUnitary (preprocess s U1 U2 V U4) := by
  exact unitary_mul (unitary_mul (unitary_mul (unitary_mul
    (FactoryPlacement.unitary _ _ h4)
    (FactoryPlacement.unitary _ _ (unitary_kron FactoryReset.unitary (Recorder.permutation_unitary _))))
    (FactoryPlacement.unitary _ _ hV)) (FactoryPlacement.unitary _ _ h2))
    (FactoryPlacement.unitary _ _ h1)

theorem kron_one_mul {a : Type} [Fintype a] [DecidableEq a] (A B : Mat a) :
    (A*B) ⊗ₖ (1 : Mat c) = (A ⊗ₖ (1 : Mat c))*(B ⊗ₖ (1 : Mat c)) := by
  rw [← mul_kronecker_mul,one_mul]

theorem circuit_factor {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4))) :
    circuit s U1 U2 V U4 =
      (FactoryResetCircuit.circuit (preprocess s U1 U2 V U4)).submatrix resetFrame resetFrame := by
  have hm (A B : Mat (Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
      ((A*B) ⊗ₖ (1 : Mat c)).submatrix frame frame =
        (A ⊗ₖ (1 : Mat c)).submatrix frame frame *
          (B ⊗ₖ (1 : Mat c)).submatrix frame frame := by
    rw [kron_one_mul]
    exact (submatrix_mul_equiv _ _ frame frame frame).symm
  rw [FactoryRegisters.circuit,first_factor,second_factor,decoder_factor,pump_factor,fourth_factor]
  rw [FactoryResetCircuit.circuit,← submatrix_mul_equiv _ _ resetFrame resetFrame resetFrame]
  change _ = resetGate * ((preprocess s U1 U2 V U4 ⊗ₖ (1 : Mat c)).submatrix frame frame)
  simp only [preprocess,hm,mul_assoc]

end ScheduleLaw.Blueprint.FactoryFreshFrame
