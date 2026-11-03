import FactoryRegisterFlags
import FactoryPacking

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryWorkState
open History FactoryRegisters FactoryWorkFlags

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def frame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    Work × (c × b × t1 × t2 × t4 × c) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((w1,w2,w3,w4),code,batch,bath1,bath2,bath4,fresh)
  invFun
    | ((w1,w2,w3,w4),code,batch,bath1,bath2,bath4,fresh) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def density (ρ : Density (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) : Density Work :=
  ⟨partialRight (ρ.matrix.submatrix frame.symm frame.symm),
    partialRight_positive (ρ.positive.submatrix _),by
      rw [partialRight_trace,submatrix_trace_equiv,ρ.normalized]⟩

theorem flag_success (ρ : Density (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)))
    (i : Fin 4) :
    FactoryWorkFlags.success (density ρ) i =
      FactoryFlagEffects.success (FactoryRegisterFlags.flag i) ρ.matrix := by
  calc
    _ = FactoryFlagEffects.success (FactoryWorkFlags.flag i) (density ρ).matrix :=
      (FactoryFlagEffects.success_sum (FactoryWorkFlags.flag i) (density ρ).matrix).symm
    _ = _ := (FactoryFlagEffects.local_success frame (FactoryWorkFlags.flag i) ρ.matrix).symm

/-- The existing sixteen-level union bound applies to the complete circuit's
physical work marginal, without imposing any diagonal-state hypothesis. -/
theorem failure (ρ : Density (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)))
    (ε1 ε2 ε4 : ℝ) (hε1 : 0 ≤ ε1) (hε4 : 0 ≤ ε4)
    (h1 : 1-ε1 ≤ FactoryFlagEffects.success (FactoryRegisterFlags.flag 0) ρ.matrix)
    (h2 : 1-ε2 ≤ FactoryFlagEffects.success (FactoryRegisterFlags.flag 1) ρ.matrix)
    (h3 : FactoryFlagEffects.success (FactoryRegisterFlags.flag 2) ρ.matrix=1)
    (h4 : (1-ε4)*(1-ε1) ≤ FactoryFlagEffects.success (FactoryRegisterFlags.flag 3) ρ.matrix) :
    1-((density ρ).matrix nominal nominal).re ≤ 2*ε1+ε2+ε4 := by
  apply four_register_bound (density ρ) ε1 ε2 ε4 hε1 hε4
  · rwa [flag_success]
  · rwa [flag_success]
  · rwa [flag_success]
  · rwa [flag_success]

end ScheduleLaw.Blueprint.FactoryWorkState
