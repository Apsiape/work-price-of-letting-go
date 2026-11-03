import FactoryRegisters
import FactoryFlagEffects
import FactoryPermutation
import FactoryWorkFlags

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryRegisterFlags
open History FactoryRegisters FactoryFlagEffects

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def flag (i : Fin 4) (z : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) : Fin 2 :=
  FactoryWorkFlags.flag i (z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1)

theorem first_success (i : Fin 4) (hi : i≠0) (U : Mat (b × (Fin 2 × t1)))
    (hU : IsUnitary U) (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag i) (evolve (FactoryPlacement.place firstFrame U) ρ)=success (flag i) ρ := by
  apply disjoint_success firstFrame (flag i)
    (fun z => FactoryWorkFlags.flag i (0,z.2.1,z.2.2.1,z.2.2.2.1)) _ U hU ρ
  intro z
  fin_cases i <;> simp_all [flag,FactoryWorkFlags.flag,firstFrame]

theorem second_success (i : Fin 4) (hi : i≠1) (U : Mat (c × (Fin 2 × t2)))
    (hU : IsUnitary U) (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag i) (evolve (FactoryPlacement.place secondFrame U) ρ)=success (flag i) ρ := by
  apply disjoint_success secondFrame (flag i)
    (fun z => FactoryWorkFlags.flag i (z.2.1,0,z.2.2.1,z.2.2.2.1)) _ U hU ρ
  intro z
  fin_cases i <;> simp_all [flag,FactoryWorkFlags.flag,secondFrame]

theorem fourth_success (i : Fin 4) (hi : i≠3) (U : Mat (c × (Fin 2 × t4)))
    (hU : IsUnitary U) (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag i) (evolve (FactoryPlacement.place fourthFrame U) ρ)=success (flag i) ρ := by
  apply disjoint_success fourthFrame (flag i)
    (fun z => FactoryWorkFlags.flag i (z.2.1,z.2.2.1,z.2.2.2.1,0)) _ U hU ρ
  intro z
  fin_cases i <;> simp_all [flag,FactoryWorkFlags.flag,fourthFrame]

theorem decoder_success (i : Fin 4) (V : Mat c) (hV : IsUnitary V)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag i) (evolve (FactoryPlacement.place resetFrame V) ρ)=success (flag i) ρ := by
  apply disjoint_success resetFrame (flag i)
    (fun z => FactoryWorkFlags.flag i
      (z.1.2.1,z.1.2.2.1,z.1.2.2.2.1,z.1.2.2.2.2.1)) _ V hV ρ
  intro z
  rfl

def resetPermutation : Equiv.Perm (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  (resetFrame.trans FactoryReset.swap).trans resetFrame.symm

theorem reset_matrix : resetGate (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)=
    resetPermutation.permMatrix ℂ := by
  ext i j
  have he : resetPermutation i=j ↔ FactoryReset.swap (resetFrame i)=resetFrame j := by
    rw [← (resetFrame (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)).injective.eq_iff]
    simp only [resetPermutation,Equiv.trans_apply,Equiv.apply_symm_apply]
  simp only [resetGate,submatrix_apply,Recorder.permutation_entry,he]

theorem reset_success (i : Fin 4)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag i) (evolve resetGate ρ)=success (flag i) ρ := by
  rw [reset_matrix]
  apply permutation_success _ _ _ ρ
  intro z
  rfl

theorem pump_success {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (i : Fin 4) (hi : i≠2)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag i) (evolve (swapPump s) ρ)=success (flag i) ρ := by
  rw [swapPump,FactoryPermutation.tensor,FactoryPermutation.place]
  apply permutation_success _ _ _ ρ
  intro z
  fin_cases i <;> simp_all [flag,FactoryWorkFlags.flag,FactoryPermutation.placed,
    swapFrame,FactoryReset.swap]

theorem pump_third {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag 2) (evolve (swapPump s) ρ)=ρ.trace.re-success (flag 2) ρ := by
  rw [swapPump,FactoryPermutation.tensor,FactoryPermutation.place,Recorder.permutation_evolve]
  let π := FactoryPermutation.placed (swapFrame (t1:=t1) (t2:=t2) (t4:=t4) s)
    (Equiv.prodCongr (FactoryReset.swap (a:=b) (b:=e)) (Fin.revPerm (n:=2)))
  have he : (fun z => opposite (flag 2) (π z))=flag 2 := by
    funext z
    rcases z with ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    fin_cases w3 <;> simp [π,opposite,flag,FactoryWorkFlags.flag,FactoryPermutation.placed,
      swapFrame,FactoryReset.swap,Fin.revPerm,Fin.rev]
  rw [← opposite_success (flag 2) ρ]
  simpa only [he] using (success_reindex π (opposite (flag 2)) ρ)

/-- A converter's work label survives every later physical gate, including
all failed columns, the residue-inclusive extraction, and controller reset. -/
theorem first_final {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag 0) (evolve (circuit s U1 U2 V U4) ρ)=
      success (flag 0) (evolve (FactoryPlacement.place firstFrame U1) ρ) := by
  simp only [circuit,evolve_mul]
  rw [reset_success,fourth_success 0 (by decide) U4 h4,pump_success s 0 (by decide),
    decoder_success 0 V hV,second_success 0 (by decide) U2 h2]

theorem second_final {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (hV : IsUnitary V) (h4 : IsUnitary U4)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    success (flag 1) (evolve (circuit s U1 U2 V U4) ρ)=
      success (flag 1) (evolve (FactoryPlacement.place secondFrame U2)
        (evolve (FactoryPlacement.place firstFrame U1) ρ)) := by
  simp only [circuit,evolve_mul]
  rw [reset_success,fourth_success 1 (by decide) U4 h4,pump_success s 1 (by decide),
    decoder_success 1 V hV]

theorem third_final {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)))
    (ht : ρ.trace=1) (hz : success (flag 2) ρ=0) :
    success (flag 2) (evolve (circuit s U1 U2 V U4) ρ)=1 := by
  simp only [circuit,evolve_mul]
  rw [reset_success,fourth_success 2 (by decide) U4 h4,pump_third]
  rw [decoder_success 2 V hV,second_success 2 (by decide) U2 h2,
    first_success 2 (by decide) U1 h1,hz]
  simp only [evolve_trace_one _ _ (FactoryPlacement.unitary _ _ hV)
    (evolve_trace_one _ _ (FactoryPlacement.unitary _ _ h2)
      (evolve_trace_one _ _ (FactoryPlacement.unitary _ _ h1) ht)),Complex.one_re,sub_zero]

end ScheduleLaw.Blueprint.FactoryRegisterFlags
