import FactoryPackedStock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPackedFormation
open History FactoryPacking FactoryPackedStock FactoryRegisterOutput

theorem auxiliary_pos {D r1 r2 r4 : ℕ} (hD : 0<D)
    (h1 : 0<r1) (h2 : 0<r2) (h4 : 0<r4) : 0<auxSize D r1 r2 r4 := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  letI : Nonempty (Fin r1) := ⟨⟨0,h1⟩⟩
  letI : Nonempty (Fin r2) := ⟨⟨0,h2⟩⟩
  letI : Nonempty (Fin r4) := ⟨⟨0,h4⟩⟩
  exact Fintype.card_pos

def formation {d m D r1 r2 r4 : ℕ} (hd : 0<d) (hm : 0 < m) (hD : 0<D)
    (h1 : 0<r1) (h2 : 0<r2) (h4 : 0<r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (FactoryRegisters.Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) : Formation β τ q m :=
  FactoryFormation.formation hd β hβ τ q hq m D 16 (auxSize D r1 r2 r4)
    hm hD (by decide) (auxiliary_pos hD h1 h2 h4) (auxHamiltonian H1 H2 H4)
    (workEnergy x1 x2 x3 x4) initial nominal
    (U.submatrix (frame d m D r1 r2 r4).symm (frame d m D r1 r2 r4).symm)
    (unitary_submatrix _ hU)

theorem charged {d m D r1 r2 r4 : ℕ} (hd : 0<d) (hm : 0 < m) (hD : 0<D)
    (h1 : 0<r1) (h2 : 0<r2) (h4 : 0<r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (FactoryRegisters.Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) :
    Driven.CapitalCharged (formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU).hardware :=
  FactoryCapital.formation_charged hd β hβ τ q hq m D 16 (auxSize D r1 r2 r4)
    hm hD (by decide) (auxiliary_pos hD h1 h2 h4) (auxHamiltonian H1 H2 H4)
    (workEnergy x1 x2 x3 x4) initial nominal _ (unitary_submatrix _ hU)

theorem debit {d m D r1 r2 r4 : ℕ} (hd : 0<d) (hm : 0 < m) (hD : 0<D)
    (h1 : 0<r1) (h2 : 0<r2) (h4 : 0<r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (FactoryRegisters.Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) :
    (formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU).debit =
      -(x1+x2+x3+x4)/(m : ℝ) := by
  change (workEnergy x1 x2 x3 x4 initial-workEnergy x1 x2 x3 x4 nominal)/(m : ℝ)=_
  rw [nominal_debit]

def stockView {b aux c w r : Type} (e : r ≃ b × aux) :
    (c × (w × r)) ≃ b × (aux × (w × c)) where
  toFun z := ((e z.2.2).1,(e z.2.2).2,z.2.1,z.1)
  invFun z := (z.2.2.2,z.2.2.1,e.symm (z.1,z.2.1))
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by simp only [Equiv.apply_symm_apply,Prod.mk.eta]

theorem reservoir_batch {b aux c w r : Type} [Fintype aux] [Fintype c] [Fintype w]
    (e : r ≃ b × aux) (ρ : Mat (c × (w × r))) :
    partialRight ((partialLeft (partialLeft ρ)).submatrix e.symm e.symm)=
      marginal (stockView e) ρ := by
  ext i j
  simp only [partialRight,partialLeft,marginal,stockView,submatrix_apply,
    Equiv.coe_fn_symm_mk,Fintype.sum_prod_type]

def batchRestFrame (D r1 r2 r4 : ℕ) :
    BatchRest (c:=Fin D) (t1:=Fin r1) (t2:=Fin r2) (t4:=Fin r4) ≃
      Fin (auxSize D r1 r2 r4) × (Fin 16 × Fin D) where
  toFun
    | (code,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (auxEquiv D r1 r2 r4 (bath1,bath2,bath4,fresh),workEquiv (w1,w2,w3,w4),code)
  invFun z :=
    let b := (auxEquiv D r1 r2 r4).symm z.1
    let w := workEquiv.symm z.2.1
    (z.2.2,w.1,w.2.1,w.2.2.1,w.2.2.2,b.1,b.2.1,b.2.2.1,b.2.2.2)
  left_inv z := by
    rcases z with ⟨code,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    simp only [Equiv.symm_apply_apply]
  right_inv z := by
    simp only [Prod.mk.eta,Equiv.apply_symm_apply]

theorem packed_batch {d m D r1 r2 r4 : ℕ}
    (ρ : Mat (FactoryRegisters.Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4))) :
    marginal (stockView (FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4)))
      (ρ.submatrix (frame d m D r1 r2 r4).symm (frame d m D r1 r2 r4).symm) =
      marginal batchFrame ρ := by
  let E := (frame d m D r1 r2 r4).trans
    (stockView (FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4)))
  change marginal E ρ=marginal batchFrame ρ
  apply reframe batchFrame E (batchRestFrame D r1 r2 r4) _ ρ
  intro z
  simp only [E,frame,gather,stockView,Equiv.trans_apply,Equiv.prodCongr_apply,
    Prod.map_apply,Equiv.refl_apply,Equiv.apply_symm_apply,batchFrame,batchRestFrame,
    Equiv.coe_fn_mk]

end ScheduleLaw.Blueprint.FactoryPackedFormation
