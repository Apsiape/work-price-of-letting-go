import FactoryInitializer
import FactoryRegisterFlags

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryInitializedFlags
open History FactoryRegisters FactoryRegisterOutput FactoryFlagEffects

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem first_stock (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    marginal firstFrame (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)=
      batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix) := by
  let T := code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ
    (SupportRun.level 0 ⊗ₖ (γ2.matrix ⊗ₖ (γ4.matrix ⊗ₖ fresh.matrix)))))
  have ht : T.trace=1 := by
    simp only [T,trace_kronecker,code.normalized,γ2.normalized,γ4.normalized,
      fresh.normalized,SupportRun.level_trace,one_mul]
  have he : (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh).submatrix
      firstFrame.symm firstFrame.symm=
      (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix)) ⊗ₖ T := by
    ext ⟨⟨u,w1,bath1⟩,v,w2,w3,w4,bath2,bath4,fresh0⟩
      ⟨⟨u',w1',bath1'⟩,v',w2',w3',w4',bath2',bath4',fresh0'⟩
    simp only [FactoryInitializer.matrix,T,submatrix_apply,firstFrame,
      Equiv.coe_fn_symm_mk,kroneckerMap_apply]
    ring
  rw [marginal,he,partialRight_kron,ht,one_smul]

theorem third_zero (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    success (FactoryRegisterFlags.flag 2) (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)=0 := by
  rw [success_sum]
  apply Finset.sum_eq_zero
  intro z hz
  rcases z with ⟨code0,batch0,w1,w2,w3,w4,bath1,bath2,bath4,fresh0⟩
  by_cases h : w3=1 <;> simp [FactoryRegisterFlags.flag,FactoryWorkFlags.flag,
    FactoryInitializer.matrix,SupportRun.level_diagonal,h]

theorem first_probability {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    success (FactoryRegisterFlags.flag 0) (evolve (circuit s U1 U2 V U4)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))=
      energy ((1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t1)))
        (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix))) := by
  rw [FactoryRegisterFlags.first_final s U1 U2 V U4 h2 hV h4]
  change success (fun z : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) => (firstFrame z).1.2.1) _=_
  rw [local_success firstFrame (fun z => z.2.1)]
  rw [FactoryPlacement.operated_marginal]
  change success (fun z : b × (Fin 2 × t1) => z.2.1)
    (evolve U1 (marginal firstFrame (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)))=_
  rw [first_stock]
  rw [success,converter_effect]

theorem second_probability {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    success (FactoryRegisterFlags.flag 1) (evolve (circuit s U1 U2 V U4)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))=
      energy ((1 : Mat c) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t2)))
        (evolve U2 (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix))) := by
  rw [FactoryRegisterFlags.second_final s U1 U2 V U4 hV h4]
  change success (fun z : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) => (secondFrame z).1.2.1) _=_
  rw [local_success secondFrame (fun z => z.2.1)]
  rw [FactoryPlacement.operated_marginal]
  change success (fun z : c × (Fin 2 × t2) => z.2.1)
    (evolve U2 (marginal secondFrame (evolve (FactoryPlacement.place firstFrame U1)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))))=_
  rw [FactoryInitializer.second_after_first U1 h1,FactoryInitializer.second_stock]
  rw [success,converter_effect]

theorem third_probability {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    success (FactoryRegisterFlags.flag 2) (evolve (circuit s U1 U2 V U4)
      (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh))=1 :=
  FactoryRegisterFlags.third_final s U1 U2 V U4 h1 h2 hV h4 _
    (FactoryInitializer.normalized code batch γ1 γ2 γ4 fresh)
    (third_zero code batch γ1 γ2 γ4 fresh)

end ScheduleLaw.Blueprint.FactoryInitializedFlags
