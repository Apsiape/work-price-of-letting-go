import FactoryFourthStock
import FactoryInitializedFlags
import FactoryConverterSuccess

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFourthSuccess
open History FactoryRegisters FactoryFlagEffects FactoryRegisterOutput

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem old_positive (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (fresh : Density c) :
    (FactoryFourthStock.oldMatrix code batch γ1 γ2 fresh).PosSemidef :=
  code.positive.kronecker (batch.positive.kronecker ((pureMatrix_positive _).kronecker
    ((pureMatrix_positive _).kronecker ((pureMatrix_positive _).kronecker
      (γ1.positive.kronecker (γ2.positive.kronecker fresh.positive))))))

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem old_normalized (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (fresh : Density c) :
    (FactoryFourthStock.oldMatrix code batch γ1 γ2 fresh).trace=1 := by
  simp only [FactoryFourthStock.oldMatrix,trace_kronecker,code.normalized,batch.normalized,
    γ1.normalized,γ2.normalized,fresh.normalized,SupportRun.level_trace,one_mul]

def codeState {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1) (γ2 : Density t2) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2))) (V : Mat c)
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) : Density c := by
  let U := FactoryFourthStock.preprocess s U1 U2 V
  let ρ := FactoryFourthStock.oldMatrix code batch γ1 γ2 fresh
  have hU : IsUnitary U := FactoryFourthStock.preprocess_unitary s U1 U2 V h1 h2 hV
  have hp := evolve_density U ρ hU (old_positive code batch γ1 γ2 fresh)
    (old_normalized code batch γ1 γ2 fresh)
  exact ⟨partialRight (evolve U ρ),partialRight_positive hp.1,by rw [partialRight_trace,hp.2]⟩

/-- The final fourth work bit is precisely the local extractor's success
probability for the actual pre-extraction code density and untouched stock. -/
theorem probability {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) :
    success (FactoryRegisterFlags.flag 3) (evolve (circuit s U1 U2 V U4)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))=
      energy ((1 : Mat c) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t4)))
        (evolve U4 ((codeState s code batch γ1 γ2 fresh U1 U2 V h1 h2 hV).matrix ⊗ₖ
          (SupportRun.level 0 ⊗ₖ γ4.matrix))) := by
  have hc : circuit s U1 U2 V U4=resetGate * FactoryPlacement.place fourthFrame U4 *
      FactoryFourthStock.before s U1 U2 V := by
    simp only [circuit,FactoryFourthStock.before,mul_assoc]
  rw [hc,evolve_mul,evolve_mul,FactoryRegisterFlags.reset_success]
  change success (fun z : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) => (fourthFrame z).1.2.1) _=_
  rw [local_success fourthFrame (fun z => z.2.1),FactoryPlacement.operated_marginal]
  change success (fun z : c × (Fin 2 × t4) => z.2.1)
    (evolve U4 (marginal fourthFrame (evolve (FactoryFourthStock.before s U1 U2 V)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))))=_
  rw [FactoryFourthStock.fourth_marginal,success,converter_effect]
  rfl

end ScheduleLaw.Blueprint.FactoryFourthSuccess
