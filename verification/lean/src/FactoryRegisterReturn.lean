import FactoryFreshFrame
import FactoryInitializer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryRegisterReturn
open History FactoryRegisters

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def oldMatrix (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) :
    Mat (FactoryFreshFrame.Old (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  code.matrix ⊗ₖ (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ
    (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ (γ1.matrix ⊗ₖ
      (γ2.matrix ⊗ₖ γ4.matrix)))))))

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem old_positive (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) :
    (oldMatrix code batch γ1 γ2 γ4).PosSemidef :=
  code.positive.kronecker (batch.positive.kronecker ((pureMatrix_positive _).kronecker
    ((pureMatrix_positive _).kronecker ((pureMatrix_positive _).kronecker
      ((pureMatrix_positive _).kronecker (γ1.positive.kronecker
        (γ2.positive.kronecker γ4.positive)))))))

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem old_normalized (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) :
    (oldMatrix code batch γ1 γ2 γ4).trace=1 := by
  simp only [oldMatrix,trace_kronecker,code.normalized,batch.normalized,γ1.normalized,
    γ2.normalized,γ4.normalized,SupportRun.level_trace,one_mul]

omit [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4] in
theorem initial_factor (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh).submatrix
      (resetFrame (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)).symm resetFrame.symm =
      ((oldMatrix code batch γ1 γ2 γ4 ⊗ₖ fresh.matrix).submatrix
        (Equiv.prodAssoc c (Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) c).symm
        (Equiv.prodAssoc c (Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) c).symm) := by
  ext ⟨code0,⟨⟨batch0,w1,w2,w3,w4,bath1,bath2,bath4⟩,fresh0⟩⟩
    ⟨code1,⟨⟨batch1,v1,v2,v3,v4,bath1',bath2',bath4'⟩,fresh1⟩⟩
  simp only [FactoryInitializer.matrix,oldMatrix,resetFrame,Equiv.coe_fn_symm_mk,
    submatrix_apply,Equiv.prodAssoc_symm_apply,kroneckerMap_apply]
  ring

/-- The literal full physical circuit restores the fresh stock as a product
with every old register, including all old correlations and retired baths. -/
theorem circuit_return {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    ∃ σ : Density ((Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c),
      (evolve (circuit s U1 U2 V U4)
        (FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh)).submatrix
          resetFrame.symm resetFrame.symm = fresh.matrix ⊗ₖ σ.matrix := by
  let U := FactoryFreshFrame.preprocess s U1 U2 V U4
  let ρ := oldMatrix code batch γ1 γ2 γ4
  have hU : IsUnitary U := FactoryFreshFrame.preprocess_unitary s U1 U2 V U4 h1 h2 hV h4
  obtain ⟨hp,ht⟩ := evolve_density U ρ hU
    (old_positive code batch γ1 γ2 γ4) (old_normalized code batch γ1 γ2 γ4)
  let σ : Density ((Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c) :=
    ⟨(evolve U ρ).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _),
      hp.submatrix _,by rw [submatrix_trace_equiv,ht]⟩
  refine ⟨σ,?_⟩
  rw [← evolve_submatrix_equiv,FactoryFreshFrame.circuit_factor]
  have he : ((FactoryResetCircuit.circuit U).submatrix resetFrame resetFrame).submatrix
      resetFrame.symm resetFrame.symm=FactoryResetCircuit.circuit U := by
    ext i j
    simp only [submatrix_apply,Equiv.apply_symm_apply]
  rw [he,initial_factor,FactoryResetCircuit.whole_rest_return]

end ScheduleLaw.Blueprint.FactoryRegisterReturn
