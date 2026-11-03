import FactoryInitializer
import FactoryCapital
import FactoryGibbsReindex
import FactoryWorkFlags

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPacking
open History FactoryRegisters FactoryWorkFlags

def gather {b c t1 t2 t4 : Type} : Registers b c t1 t2 t4 ≃
    c × (Work × (b × (t1 × t2 × t4 × c))) where
  toFun
    | (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh) =>
      (code,(w1,w2,w3,w4),batch,bath1,bath2,bath4,fresh)
  invFun
    | (code,(w1,w2,w3,w4),batch,bath1,bath2,bath4,fresh) =>
      (code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def workEquiv : Work ≃ Fin 16 :=
  (Fintype.equivFin Work).trans (finCongr (by decide))

def initial : Fin 16 := workEquiv (0,0,0,0)
def nominal : Fin 16 := workEquiv FactoryWorkFlags.nominal

abbrev Aux (D r1 r2 r4 : ℕ) := Fin r1 × Fin r2 × Fin r4 × Fin D

def auxSize (D r1 r2 r4 : ℕ) := Fintype.card (Aux D r1 r2 r4)

def auxEquiv (D r1 r2 r4 : ℕ) : Aux D r1 r2 r4 ≃ Fin (auxSize D r1 r2 r4) :=
  Fintype.equivFin _

/-- Pack all original registers into the literal controller/work/reservoir
split expected by Formation; no stock or coding residue is omitted. -/
def frame (d m D r1 r2 r4 : ℕ) :
    Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4) ≃
      Fin D × (Fin 16 × Fin ((Fintype.card (Fin m → Fin d))*auxSize D r1 r2 r4)) :=
  gather.trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr workEquiv
      ((Equiv.prodCongr (Equiv.refl _) (auxEquiv D r1 r2 r4)).trans
        (FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4)).symm)))

def auxHamiltonian {D r1 r2 r4 : ℕ}
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4)) :
    Hamiltonian (Fin (auxSize D r1 r2 r4)) :=
  FactoryGibbs.reindexHamiltonian (auxEquiv D r1 r2 r4).symm
    (FactoryGibbs.sumHamiltonian H1 (FactoryGibbs.sumHamiltonian H2
      (FactoryGibbs.sumHamiltonian H4 (FiniteFlat.zeroHamiltonian D))))

theorem auxiliary_stock {D r1 r2 r4 : ℕ} (hD : 0<D) (β : ℝ)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4)) :
    gibbs β (auxHamiltonian (D:=D) H1 H2 H4) =
      (gibbs β H1 ⊗ₖ (gibbs β H2 ⊗ₖ (gibbs β H4 ⊗ₖ
        (FactoryFormation.flat D hD).matrix))).submatrix
          (auxEquiv D r1 r2 r4).symm (auxEquiv D r1 r2 r4).symm := by
  rw [auxHamiltonian,FactoryGibbs.gibbs_reindex,FactoryGibbs.gibbs_product,
    FactoryGibbs.gibbs_product,FactoryGibbs.gibbs_product,FactoryCapital.zero_gibbs β D hD]

theorem reservoir_stock {d D r1 r2 r4 : ℕ} (hD : 0<D) (β : ℝ) (hβ : β≠0)
    (q : Density (Fin d)) (hq : q.matrix.PosDef) (m : ℕ)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4)) :
    gibbs β (FactoryFormation.reservoir (m:=m) β q (auxHamiltonian (D:=D) H1 H2 H4)) =
      (tensorPower q.matrix m ⊗ₖ
        ((gibbs β H1 ⊗ₖ (gibbs β H2 ⊗ₖ (gibbs β H4 ⊗ₖ
          (FactoryFormation.flat D hD).matrix))).submatrix
            (auxEquiv D r1 r2 r4).symm (auxEquiv D r1 r2 r4).symm)).submatrix
          (FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4))
          (FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4)) := by
  rw [FactoryFormation.reservoir,FactoryGibbs.gibbs_reindex,
    FactoryTensor.batch_aux_stock β hβ q hq,auxiliary_stock hD]

def workEnergy (x1 x2 x3 x4 : ℝ) (w : Fin 16) : ℝ :=
  let j := workEquiv.symm w
  (if j.1=1 then x1 else 0)+(if j.2.1=1 then x2 else 0)+
    (if j.2.2.1=1 then x3 else 0)+(if j.2.2.2=1 then x4 else 0)

theorem nominal_debit (x1 x2 x3 x4 : ℝ) :
    workEnergy x1 x2 x3 x4 initial-workEnergy x1 x2 x3 x4 nominal=-(x1+x2+x3+x4) := by
  simp only [workEnergy,initial,nominal,Equiv.symm_apply_apply,FactoryWorkFlags.nominal,
    Fin.zero_ne_one,if_false,if_true,add_zero,zero_add,zero_sub]

end ScheduleLaw.Blueprint.FactoryPacking
