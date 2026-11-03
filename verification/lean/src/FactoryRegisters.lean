import FactoryPlacement
import FactoryReset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryRegisters
open History

/-- Literal retained registers, including every retired stock and the fresh
 reset stock. The four work labels remain distinct even at zero gap. -/
abbrev Registers (b c t1 t2 t4 : Type) :=
  c × b × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

abbrev R := Registers b c t1 t2 t4

def firstFrame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (b × (Fin 2 × t1)) × (c × Fin 2 × Fin 2 × Fin 2 × t2 × t4 × c) where
  toFun z := ((z.2.1,z.2.2.1,z.2.2.2.2.2.2.1),z.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.2)
  invFun | ((batch,w1,bath1),code,w2,w3,w4,bath2,bath4,fresh) =>
            ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
  left_inv _ := rfl
  right_inv _ := rfl

def secondFrame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (c × (Fin 2 × t2)) × (b × Fin 2 × Fin 2 × Fin 2 × t1 × t4 × c) where
  toFun z := ((z.1,z.2.2.2.1,z.2.2.2.2.2.2.2.1),z.2.1,z.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.2)
  invFun | ((code,w2,bath2),batch,w1,w3,w4,bath1,bath4,fresh) =>
            ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fourthFrame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    (c × (Fin 2 × t4)) × (b × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × c) where
  toFun z := ((z.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.1),z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.2)
  invFun | ((code,w4,bath4),batch,w1,w2,w3,bath1,bath2,fresh) =>
            ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev Rest := b × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4

def resetFrame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    c × ((Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c) where
  toFun z := (z.1,(z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.1),z.2.2.2.2.2.2.2.2.2)
  invFun | (code,(batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh) =>
            ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
  left_inv _ := rfl
  right_inv _ := rfl

def swapFrame {e : Type} (codeSplit : c ≃ b × e) :
    R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
      ((b × (e × b)) × Fin 2) × (Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c) where
  toFun z := ((((codeSplit z.1).1,(codeSplit z.1).2,z.2.1),z.2.2.2.2.1),
    z.2.2.1,z.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2.2.2)
  invFun | (((cb,ce,batch),w3),w1,w2,w4,bath1,bath2,bath4,fresh) =>
            ⟨codeSplit.symm (cb,ce),batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
  left_inv z := by rcases z with ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨⟨cb,ce,batch⟩,w3⟩,w1,w2,w4,bath1,bath2,bath4,fresh⟩; simp only [Equiv.apply_symm_apply]

def resetGate : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  ((FactoryReset.swap (a:=c) (b:=Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4))).permMatrix ℂ).submatrix
    resetFrame resetFrame

omit [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem reset_unitary : IsUnitary (resetGate (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  unitary_submatrix resetFrame FactoryReset.unitary

def swapPump {e : Type} [Fintype e] [DecidableEq e] (codeSplit : c ≃ b × e) :
    Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  FactoryPlacement.place (swapFrame codeSplit)
    ((FactoryReset.swap (a:=b) (b:=e)).permMatrix ℂ ⊗ₖ (Fin.revPerm (n:=2)).permMatrix ℂ)

omit [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem swapPump_unitary {e : Type} [Fintype e] [DecidableEq e] (codeSplit : c ≃ b × e) :
    IsUnitary (swapPump (t1:=t1) (t2:=t2) (t4:=t4) codeSplit) :=
  FactoryPlacement.unitary _ _ (unitary_kron FactoryReset.unitary (Recorder.permutation_unitary _))

/-- The actual full square before the common conserving phase compilation. -/
def circuit {e : Type} [Fintype e] [DecidableEq e] (codeSplit : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4))) :
    Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  resetGate * FactoryPlacement.place fourthFrame U4 * swapPump codeSplit *
    FactoryPlacement.place resetFrame V * FactoryPlacement.place secondFrame U2 *
      FactoryPlacement.place firstFrame U1

theorem circuit_unitary {e : Type} [Fintype e] [DecidableEq e] (codeSplit : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    IsUnitary (circuit codeSplit U1 U2 V U4) := by
  exact unitary_mul (unitary_mul (unitary_mul (unitary_mul (unitary_mul
    reset_unitary (FactoryPlacement.unitary _ _ h4)) (swapPump_unitary codeSplit))
      (FactoryPlacement.unitary _ _ hV)) (FactoryPlacement.unitary _ _ h2))
        (FactoryPlacement.unitary _ _ h1)

end ScheduleLaw.Blueprint.FactoryRegisters
