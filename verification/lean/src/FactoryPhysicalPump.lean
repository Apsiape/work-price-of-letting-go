import FactoryPumpEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPhysicalPump
open History FactoryRegisters FactoryRegisterOutput FactoryPhysicalHamiltonian FactoryPumpEnergy

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def restHamiltonian (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4) (x1 x2 x4 : ℝ) :
    Mat (Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c) :=
  sumH (work x1) <| sumH (work x2) <| sumH (work x4) <|
    sumH H1 <| sumH H2 <| sumH H4 (0 : Mat c)

theorem pump_frame {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4) (x1 x2 x3 x4 : ℝ) :
    hamiltonian (c:=c) H H1 H2 H4 x1 x2 x3 x4 =
      (sumH (FactorySwapEnergy.hamiltonian H x3)
        (restHamiltonian (c:=c) H1 H2 H4 x1 x2 x4)).submatrix (swapFrame s) (swapFrame s) := by
  ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
  have hs : (if (s code).1=(s code').1 then (1 : ℂ) else 0) *
      (if (s code).2=(s code').2 then (1 : ℂ) else 0)=if code=code' then 1 else 0 := by
    rw [← indicator_and]
    simp only [← Prod.ext_iff,s.injective.eq_iff]
  simp only [hamiltonian,FactorySwapEnergy.hamiltonian,FactorySwapEnergy.batchHamiltonian,
    restHamiltonian,sumH,work,swapFrame,Equiv.coe_fn_mk,submatrix_apply,kroneckerMap_apply,
    add_apply,Matrix.zero_apply,Matrix.one_apply,Prod.mk.injEq,indicator_and,
    zero_mul,zero_add,mul_zero,add_zero]
  rw [← hs]
  ring

/-- The complete retained energy change of the pump, including all baths.
The hypotheses are the actual input trace and third work marginal only. -/
theorem pump_change {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4) (x1 x2 x4 Eg Ecode : ℝ)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)))
    (ht : ρ.trace=1) (hz : FactoryFlagEffects.success (FactoryRegisterFlags.flag 2) ρ=0) :
    let K := hamiltonian (c:=c) H H1 H2 H4 x1 x2 (Eg-Ecode) x4
    let σ := marginal (swapFrame s) ρ
    energy K (evolve (swapPump s) ρ)-energy K ρ =
      (energy H (partialRight (partialRight σ))-Ecode) +
        (Eg-energy H (partialRight ((partialRight σ).submatrix
          FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm))) := by
  dsimp only
  have htrace : (marginal (swapFrame s) ρ).trace=1 := by
    rw [marginal,partialRight_trace,submatrix_trace_equiv,ht]
  change FactoryFlagEffects.success (fun z => ((swapFrame s) z).1.2) ρ=0 at hz
  rw [FactoryFlagEffects.local_success,last_success] at hz
  rw [pump_frame s]
  rw [show swapPump (t1:=t1) (t2:=t2) (t4:=t4) s =
      FactoryPlacement.place (swapFrame s)
        (((FactoryReset.swap (a:=b) (b:=e)).permMatrix ℂ) ⊗ₖ
          ((Fin.revPerm (n:=2)).permMatrix ℂ)) from rfl]
  rw [placed_change (swapFrame s) _ _ _
    (unitary_kron FactoryReset.unitary (Recorder.permutation_unitary _))]
  exact local_change H _ htrace hz Eg Ecode

end ScheduleLaw.Blueprint.FactoryPhysicalPump
