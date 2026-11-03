import FactoryDriven
import FactoryCoding
import FactoryTensorStock
import FactoryGibbsReindex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFormation
open History

def inventory : Inventory where
  count := 0
  dim := Fin.elim0
  dim_pos c := Fin.elim0 c
  H c := Fin.elim0 c

def schedule : Schedule inventory where
  visits := 0
  carrier := Fin.elim0
  position := by
    change (Fin 0 × Bool) ≃ Fin 0
    exact Equiv.equivOfIsEmpty _ _
  ordered v := Fin.elim0 v
  disjoint v := Fin.elim0 v

def flat (c : ℕ) (hc : 0 < c) : Density (Fin c) :=
  FactoryCoding.flatDensity 1 (by simp [Matrix.IsHermitian]) (by simp) c hc (by simp)

def reservoirSplit (d m aux : ℕ) :
    Fin ((Fintype.card (Fin m → Fin d))*aux) ≃ (Fin m → Fin d) × Fin aux :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Fintype.equivFin _).symm (Equiv.refl _))

def reservoir {d m aux : ℕ} (β : ℝ) (q : Density (Fin d)) (HA : Hamiltonian (Fin aux)) :
    Hamiltonian (Fin ((Fintype.card (Fin m → Fin d))*aux)) :=
  FactoryGibbs.reindexHamiltonian (reservoirSplit d m aux)
    (FactoryGibbs.sumHamiltonian (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) m) HA)

/-- Pack a literal finite factory unitary into the original Formation type.
 The only nonstructural hypotheses are the original faithful Gibbs reference
 and positive finite dimensions; no factory accuracy or work claim is assumed. -/
def formation {d : ℕ} (hd : 0<d) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef) (m c w aux : ℕ)
    (hm : 0 < m) (hc : 0 < c) (hw : 0 < w) (haux : 0 < aux)
    (HA : Hamiltonian (Fin aux)) (E : Fin w → ℝ) (initial nominal : Fin w)
    (U : Mat (Fin c × (Fin w × Fin ((Fintype.card (Fin m → Fin d))*aux))))
    (hU : IsUnitary U) : Formation β τ q m := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin aux) := ⟨⟨0,haux⟩⟩
  let r := (Fintype.card (Fin m → Fin d))*aux
  have hr : 0<r := Nat.mul_pos Fintype.card_pos haux
  let HR := reservoir (m:=m) β q HA
  let p := FactoryDriven.hardware schedule β c w r hc hw hr (flat c hc)
    (FiniteFlat.zeroHamiltonian c) HR E initial nominal 0 U hU
  refine {
    inventory := inventory
    schedule := schedule
    empty := rfl
    hardware := p
    aux := aux
    aux_pos := haux
    reservoirSplit := reservoirSplit d m aux
    auxiliaryHamiltonian := HA
    reservoirHamiltonian := ?_
    initial_batch := ?_
    debit := (E initial-E nominal)/(m : ℝ)
    debit_eq := ?_ }
  · change (reservoir (m:=m) β q HA).matrix.submatrix (reservoirSplit d m aux).symm
      (reservoirSplit d m aux).symm = _
    ext i j
    simp only [reservoir,FactoryGibbs.reindexHamiltonian,submatrix_apply,
      Equiv.apply_symm_apply,FactoryGibbs.sumHamiltonian,FactoryTensor.hamiltonian,
      FactoryGibbs.tangent]
  · change partialRight ((gibbs β (reservoir (m:=m) β q HA)).submatrix
      (reservoirSplit d m aux).symm (reservoirSplit d m aux).symm)=_
    rw [reservoir,FactoryGibbs.gibbs_reindex]
    have he : ((gibbs β (FactoryGibbs.sumHamiltonian
        (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) m) HA)).submatrix
        (reservoirSplit d m aux) (reservoirSplit d m aux)).submatrix
        (reservoirSplit d m aux).symm (reservoirSplit d m aux).symm =
          gibbs β (FactoryGibbs.sumHamiltonian (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) m) HA) := by
      ext i j
      simp only [submatrix_apply,Equiv.apply_symm_apply]
    rw [he,FactoryTensor.batch_aux_stock β hβ q hq m HA,
      partialRight_kron,gibbs_trace,one_smul]
  · change E initial-E nominal=(m : ℝ)*((E initial-E nominal)/(m : ℝ))
    field_simp

end ScheduleLaw.Blueprint.FactoryFormation
