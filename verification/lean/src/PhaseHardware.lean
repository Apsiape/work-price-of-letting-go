import BlueprintContracts
import FactoryGibbsReindex
import FactoryGibbsProduct
import FactoryCircuit
import IdleExtension

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseHardware
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def rearrange (c w r D : ℕ) :
    (Fin c × (Fin w × Fin r)) × Fin D ≃ (Fin c × Fin D) × (Fin w × Fin r) where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def split (p : Driven S β) (D : ℕ) :
    Fin (p.extension.b*D) ≃ Fin (p.c*D) × (Fin p.w × Fin p.r) :=
  (finProdFinEquiv.symm.trans (Equiv.prodCongr p.split (Equiv.refl (Fin D)))).trans
    ((rearrange p.c p.w p.r D).trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)))

theorem split_apply (p : Driven S β) (D : ℕ) (i : Fin (p.extension.b*D)) :
    split p D i=(finProdFinEquiv ((p.split (finProdFinEquiv.symm i).1).1,(finProdFinEquiv.symm i).2),
      (p.split (finProdFinEquiv.symm i).1).2) := rfl

def controller (p : Driven S β) {D : ℕ} (φ : Density (Fin D)) : Density (Fin (p.c*D)) :=
  ⟨(p.controller.matrix ⊗ₖ φ.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm,
    (p.controller.positive.kronecker φ.positive).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,p.controller.normalized,φ.normalized,mul_one]⟩

def HC (p : Driven S β) {D : ℕ} (Hφ : Hamiltonian (Fin D)) : Hamiltonian (Fin (p.c*D)) :=
  FactoryGibbs.reindexHamiltonian finProdFinEquiv.symm (FactoryGibbs.sumHamiltonian p.HC Hφ)

def phaseStock {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) : Extension S :=
  FactoryCircuit.bodyCircuit S hD φ 1 (by constructor <;> simp)

def extension (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k)) : Extension S :=
  { IdleExtension.extension p.extension (phaseStock hD φ) with
    gate := G
    unitary := hG
    gate_local := hlocal }

/-- The same original battery and every original Gibbs stock are retained;
the complete finite phase is explicitly charged to the controller. -/
def hardware (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k)) : Driven S β where
  extension := extension p hD φ G hG hlocal
  c := p.c*D
  w := p.w
  r := p.r
  c_pos := Nat.mul_pos p.c_pos hD
  w_pos := p.w_pos
  r_pos := p.r_pos
  split := split p D
  controller := controller p φ
  HC := HC p Hφ
  HR := p.HR
  batteryEnergy := p.batteryEnergy
  initialLevel := p.initialLevel
  nominalLevel := p.nominalLevel
  capital := faithfulRelativeEntropy (controller p φ).matrix (gibbs β (HC p Hφ))/β
  source_product := by
    change (p.extension.source.matrix ⊗ₖ φ.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm=
      ((PhaseHardware.controller p φ).matrix ⊗ₖ
        (pureMatrix (fun j : Fin p.w => if j=p.initialLevel then 1 else 0) ⊗ₖ gibbs β p.HR)).submatrix
          (PhaseHardware.split p D) (PhaseHardware.split p D)
    rw [p.source_product]
    ext i j
    simp only [submatrix_apply,kroneckerMap_apply,PhaseHardware.split_apply,PhaseHardware.controller,Equiv.trans_apply,
      Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
    ring

theorem capital_charged (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k)) :
    Driven.CapitalCharged (hardware p hD φ Hφ G hG hlocal) := le_rfl

theorem nominal_debit (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k)) :
    Driven.nominalDebit (hardware p hD φ Hφ G hG hlocal)=Driven.nominalDebit p := rfl

/-- Upgrade exactly the same hardware once each actual contact is proved
conserving its declared, fixed body-plus-carrier Hamiltonian. -/
def toEngine (p : Driven S β)
    (hcon : ∀ k,Conserves (p.extension.gate k)
      (p.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+(1 : Mat (Fin p.extension.b)) ⊗ₖ payloadHamiltonian I)) :
    Engine S β where
  extension := p.extension
  c := p.c
  w := p.w
  r := p.r
  c_pos := p.c_pos
  w_pos := p.w_pos
  r_pos := p.r_pos
  split := p.split
  controller := p.controller
  HC := p.HC
  HR := p.HR
  batteryEnergy := p.batteryEnergy
  initialLevel := p.initialLevel
  nominalLevel := p.nominalLevel
  capital := p.capital
  source_product := p.source_product
  gate_conserves := hcon

end ScheduleLaw.Blueprint.PhaseHardware
