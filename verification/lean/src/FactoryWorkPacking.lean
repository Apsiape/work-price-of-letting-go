import FactoryWorkState
import FactoryFormedOutput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryWorkPacking
open History FactoryRegisters FactoryPacking FactoryPackedFormation FactoryRegisterOutput

def workView {c w r : Type} : c × (w × r) ≃ w × (r × c) where
  toFun z := (z.2.1,z.2.2,z.1)
  invFun z := (z.2.2,z.1,z.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem work_marginal {c w r : Type} [Fintype c] [Fintype r]
    (ρ : Mat (c × (w × r))) :
    partialRight (partialLeft ρ)=marginal workView ρ := by
  ext i j
  simp only [partialRight,partialLeft,marginal,workView,submatrix_apply,
    Equiv.coe_fn_symm_mk,Fintype.sum_prod_type]

def restFrame (d m D r1 r2 r4 : ℕ) :
    (Fin D × (Fin m → Fin d) × Fin r1 × Fin r2 × Fin r4 × Fin D) ≃
      Fin ((Fintype.card (Fin m → Fin d))*auxSize D r1 r2 r4) × Fin D where
  toFun
    | (code,batch,bath1,bath2,bath4,fresh) =>
      ((FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4)).symm
        (batch,auxEquiv D r1 r2 r4 (bath1,bath2,bath4,fresh)),code)
  invFun z :=
    let r := FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4) z.1
    let b := (auxEquiv D r1 r2 r4).symm r.2
    (z.2,r.1,b.1,b.2.1,b.2.2.1,b.2.2.2)
  left_inv z := by
    rcases z with ⟨code,batch,bath1,bath2,bath4,fresh⟩
    simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  right_inv z := by
    simp only [Prod.mk.eta,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

/-- The literal sixteen-level battery is the full four-bit physical marginal. -/
theorem packed_battery {d m D r1 r2 r4 : ℕ}
    (ρ : Mat (Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4))) :
    partialRight (partialLeft (ρ.submatrix (FactoryPacking.frame d m D r1 r2 r4).symm
      (FactoryPacking.frame d m D r1 r2 r4).symm))=
      (marginal FactoryWorkState.frame ρ).submatrix workEquiv.symm workEquiv.symm := by
  rw [work_marginal]
  let E := (FactoryWorkState.frame (b:=Fin m → Fin d) (c:=Fin D)
    (t1:=Fin r1) (t2:=Fin r2) (t4:=Fin r4)).trans
      (Equiv.prodCongr workEquiv (Equiv.refl _))
  let F := (FactoryPacking.frame d m D r1 r2 r4).trans workView
  change marginal F ρ=_
  rw [reframe E F (restFrame d m D r1 r2 r4) (by intro z; rfl) ρ]
  rfl

/-- The actual Formation battery output, in every coherent tester run, is
the same physical four-register work marginal. -/
theorem output {d m D r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) :
    let F := formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU
    ∀ z (t : Tester F.schedule z),
      Driven.batteryFinal F.hardware t =
        (marginal FactoryWorkState.frame (evolve U
          (FactoryInitializer.matrix (FactoryFormation.flat D hD)
            (W2.tensorFamilyDensity (fun _ : Fin m => q))
            (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
            (FactoryPackedStock.gibbsDensity h4 β H4) (FactoryFormation.flat D hD)))).submatrix
              workEquiv.symm workEquiv.symm := by
  dsimp only
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let A := auxSize D r1 r2 r4
  have hA : 0 < A := auxiliary_pos hD h1 h2 h4
  have hR : 0 < (Fintype.card (Fin m → Fin d))*A := Nat.mul_pos Fintype.card_pos hA
  let HR := FactoryFormation.reservoir (m:=m) β q (auxHamiltonian (D:=D) H1 H2 H4)
  let J := FactoryPacking.frame d m D r1 r2 r4
  let source := (FactoryFormation.flat D hD).matrix ⊗ₖ (FactoryPackedStock.basis initial ⊗ₖ gibbs β HR)
  let input := FactoryInitializer.matrix (FactoryFormation.flat D hD)
    (W2.tensorFamilyDensity (fun _ : Fin m => q))
    (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
    (FactoryPackedStock.gibbsDensity h4 β H4) (FactoryFormation.flat D hD)
  have hs : source=input.submatrix J.symm J.symm := by
    have he := FactoryPackedStock.initialized_registers hD h1 h2 h4 β hβ q hq m H1 H2 H4
    ext i j
    have hh := congrArg (fun M => M (J.symm i) (J.symm j)) he
    simpa only [submatrix_apply,J,Equiv.apply_symm_apply,source,HR,input] using hh
  let F := formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU
  intro z t
  have hb := FactoryDriven.output FactoryFormation.schedule rfl β D 16
    ((Fintype.card (Fin m → Fin d))*A) hD (by decide) hR
    (FactoryFormation.flat D hD) (FiniteFlat.zeroHamiltonian D) HR
    (workEnergy x1 x2 x3 x4) initial nominal 0 (U.submatrix J.symm J.symm)
    (unitary_submatrix J.symm hU) t
  change (bodyOutput F.hardware.extension t).submatrix F.hardware.split.symm
    F.hardware.split.symm = evolve (U.submatrix J.symm J.symm) source at hb
  change partialRight (partialLeft ((bodyOutput F.hardware.extension t).submatrix
    F.hardware.split.symm F.hardware.split.symm))=_
  rw [hb,hs,evolve_submatrix_equiv]
  exact packed_battery (evolve U input)

end ScheduleLaw.Blueprint.FactoryWorkPacking
