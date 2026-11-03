import FactorySwapOutput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryInitializer
open History FactoryRegisters FactoryRegisterOutput

variable {b c r t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype r] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq r]
  [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def matrix (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  code.matrix ⊗ₖ (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ
    (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ (γ1.matrix ⊗ₖ
      (γ2.matrix ⊗ₖ (γ4.matrix ⊗ₖ fresh.matrix))))))))

theorem normalized (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    (matrix code batch γ1 γ2 γ4 fresh).trace=1 := by
  simp only [matrix,trace_kronecker,code.normalized,batch.normalized,γ1.normalized,
    γ2.normalized,γ4.normalized,fresh.normalized,SupportRun.level_trace,one_mul]

theorem positive (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    (matrix code batch γ1 γ2 γ4 fresh).PosSemidef :=
  code.positive.kronecker (batch.positive.kronecker ((pureMatrix_positive _).kronecker
    ((pureMatrix_positive _).kronecker ((pureMatrix_positive _).kronecker
      ((pureMatrix_positive _).kronecker (γ1.positive.kronecker
        (γ2.positive.kronecker (γ4.positive.kronecker fresh.positive))))))))

theorem second_stock (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c) :
    marginal secondFrame (matrix code batch γ1 γ2 γ4 fresh)=
      code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix) := by
  let T := batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ (SupportRun.level 0 ⊗ₖ
    (SupportRun.level 0 ⊗ₖ (γ1.matrix ⊗ₖ (γ4.matrix ⊗ₖ fresh.matrix)))))
  have ht : T.trace=1 := by
    simp only [T,trace_kronecker,batch.normalized,γ1.normalized,γ4.normalized,
      fresh.normalized,SupportRun.level_trace,one_mul]
  have he : (matrix code batch γ1 γ2 γ4 fresh).submatrix secondFrame.symm secondFrame.symm =
      (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix)) ⊗ₖ T := by
    ext ⟨⟨u,w2,bath2⟩,v,w1,w3,w4,bath1,bath4,fresh0⟩
      ⟨⟨u',w2',bath2'⟩,v',w1',w3',w4',bath1',bath4',fresh0'⟩
    simp only [matrix,T,submatrix_apply,secondFrame,Equiv.coe_fn_symm_mk,kroneckerMap_apply]
    ring
  rw [marginal,he,partialRight_kron,ht,one_smul]

def firstRestFrame : (c × Fin 2 × Fin 2 × Fin 2 × t2 × t4 × c) ≃
    (c × (Fin 2 × t2)) × (Fin 2 × Fin 2 × t4 × c) where
  toFun
    | (code,w2,w3,w4,bath2,bath4,fresh) => ((code,w2,bath2),w3,w4,bath4,fresh)
  invFun
    | ((code,w2,bath2),w3,w4,bath4,fresh) => (code,w2,w3,w4,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def secondRestFrame : (b × Fin 2 × Fin 2 × Fin 2 × t1 × t4 × c) ≃
    (b × (Fin 2 × t1)) × (Fin 2 × Fin 2 × t4 × c) where
  toFun
    | (batch,w1,w3,w4,bath1,bath4,fresh) => ((batch,w1,bath1),w3,w4,bath4,fresh)
  invFun
    | ((batch,w1,bath1),w3,w4,bath4,fresh) => (batch,w1,w3,w4,bath1,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

theorem second_after_first (U : Mat (b × (Fin 2 × t1))) (hU : IsUnitary U)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal secondFrame (evolve (FactoryPlacement.place firstFrame U) ρ)=
      marginal secondFrame ρ := by
  let E := FactoryMarginals.outsideFrame (firstFrame (b:=b) (c:=c)
    (t1:=t1) (t2:=t2) (t4:=t4)) firstRestFrame
  have hr (σ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
      marginal E σ=marginal secondFrame σ :=
    reframe secondFrame E secondRestFrame (by intro z; rfl) σ
  rw [← hr,← hr ρ]
  exact FactoryMarginals.disjoint_marginal firstFrame firstRestFrame U hU ρ

def codeRest : ((Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c) ≃
    (Fin 2 × t2) × (b × Fin 2 × Fin 2 × Fin 2 × t1 × t4 × c) where
  toFun
    | ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh) =>
      ((w2,bath2),batch,w1,w3,w4,bath1,bath4,fresh)
  invFun
    | ((w2,bath2),batch,w1,w3,w4,bath1,bath4,fresh) =>
      ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh)
  left_inv _ := rfl
  right_inv _ := rfl

theorem code_from_second
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal resetFrame ρ=partialRight (marginal secondFrame ρ) := by
  let E := (secondFrame (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)).trans
    (Equiv.prodAssoc c (Fin 2 × t2) (b × Fin 2 × Fin 2 × Fin 2 × t1 × t4 × c))
  rw [← reframe resetFrame E codeRest (by intro z; rfl) ρ]
  ext i j
  simp only [marginal,partialRight,submatrix_apply,E,Equiv.symm_trans_apply,
    Equiv.prodAssoc_symm_apply,Fintype.sum_prod_type]

/-- The complete physical circuit's emitted batch depends on the exact
unconditional second-converter run. The first preparation, later extraction,
and final reset all retain their full physical failure columns. -/
theorem circuit_output (e : c ≃ b × r)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h4 : IsUnitary U4) :
    marginal batchFrame (evolve (circuit e U1 U2 V U4)
      (matrix code batch γ1 γ2 γ4 fresh)) =
      partialRight ((evolve V (partialRight (evolve U2
        (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix))))).submatrix e.symm e.symm) := by
  rw [FactorySwapOutput.circuit_batch e U1 U2 V U4 h4,code_from_second]
  rw [show marginal secondFrame
      (evolve (FactoryPlacement.place secondFrame U2)
        (evolve (FactoryPlacement.place firstFrame U1) (matrix code batch γ1 γ2 γ4 fresh))) =
      evolve U2 (marginal secondFrame
        (evolve (FactoryPlacement.place firstFrame U1) (matrix code batch γ1 γ2 γ4 fresh))) from
        FactoryPlacement.operated_marginal secondFrame U2 _]
  rw [second_after_first U1 h1,second_stock]

end ScheduleLaw.Blueprint.FactoryInitializer
