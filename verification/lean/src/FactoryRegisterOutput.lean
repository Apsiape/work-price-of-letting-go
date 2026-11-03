import FactoryMarginals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryRegisterOutput
open History FactoryRegisters

def marginal {a b c : Type} [Fintype c] (e : a ≃ b × c) (ρ : Mat a) : Mat b :=
  partialRight (ρ.submatrix e.symm e.symm)

theorem reframe {a b c t : Type} [Fintype c] [Fintype t]
    (e : a ≃ b × c) (f : a ≃ b × t) (g : c ≃ t)
    (h : ∀ z,f z=((e z).1,g (e z).2)) (ρ : Mat a) :
    marginal f ρ=marginal e ρ := by
  have hi (i : b) (k : c) : f.symm (i,g k)=e.symm (i,k) := by
    apply f.injective
    rw [f.apply_symm_apply,h,e.apply_symm_apply]
  ext i j
  have hs := Equiv.sum_comp g (fun k => ρ (f.symm (i,k)) (f.symm (j,k)))
  simp_rw [hi] at hs
  exact hs.symm

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

abbrev BatchRest := c × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4 × c

def batchFrame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
    b × BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (batch,code,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  invFun
    | (batch,code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def fourthRest : BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
      (c × (Fin 2 × t4)) × (Fin 2 × Fin 2 × Fin 2 × t1 × t2 × c) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((code,w4,bath4),w1,w2,w3,bath1,bath2,fresh)
  invFun
    | ((code,w4,bath4),w1,w2,w3,bath1,bath2,fresh) =>
      (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual residue-inclusive extractor leaves the emitted physical batch
unchanged, for arbitrary input correlations and every failed work column. -/
theorem batch_after_fourth (U : Mat (c × (Fin 2 × t4))) (hU : IsUnitary U)
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame (evolve (FactoryPlacement.place fourthFrame U) ρ)=
      marginal batchFrame ρ := by
  classical
  let f := Equiv.refl (b × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × c)
  let E := FactoryMarginals.outsideFrame (fourthFrame (b:=b) (c:=c)
      (t1:=t1) (t2:=t2) (t4:=t4)) f
  have hr (σ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
      marginal E σ=marginal batchFrame σ :=
    reframe batchFrame E fourthRest (by intro z; rfl) σ
  rw [← hr,← hr ρ]
  exact FactoryMarginals.disjoint_marginal fourthFrame f U hU ρ

def endpointFrame : R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
      (c × c) × (b × Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((code,fresh),batch,w1,w2,w3,w4,bath1,bath2,bath4)
  invFun
    | ((code,fresh),batch,w1,w2,w3,w4,bath1,bath2,bath4) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def endpointRest : BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4) ≃
      (c × c) × (Fin 2 × Fin 2 × Fin 2 × Fin 2 × t1 × t2 × t4) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      ((code,fresh),w1,w2,w3,w4,bath1,bath2,bath4)
  invFun
    | ((code,fresh),w1,w2,w3,w4,bath1,bath2,bath4) =>
      (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def resetRest : Equiv.Perm (BatchRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (fresh,w1,w2,w3,w4,bath1,bath2,bath4,code)
  invFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (fresh,w1,w2,w3,w4,bath1,bath2,bath4,code)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The final controller/fresh-stock swap preserves the complete emitted batch. -/
theorem batch_after_reset
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    marginal batchFrame (evolve resetGate ρ)=marginal batchFrame ρ := by
  classical
  have he : evolve resetGate ρ =
      (evolve ((FactoryReset.swap (a:=c) (b:=Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4))).permMatrix ℂ)
        (ρ.submatrix resetFrame.symm resetFrame.symm)).submatrix resetFrame resetFrame := by
    rw [← evolve_submatrix_equiv]
    congr 1
  rw [he,Recorder.permutation_evolve]
  ext i j
  have hs := Equiv.sum_comp (resetRest (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))
      (fun k => ρ (batchFrame.symm (i,k)) (batchFrame.symm (j,k)))
  exact hs

end ScheduleLaw.Blueprint.FactoryRegisterOutput
