import PhaseHardwareEnergy
import SourceFunctional
import FactoryEnergyTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseEnergyRefund
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

theorem conserving_defect_zero (p : Driven S β)
    (hcon : ∀ k,Conserves (p.extension.gate k)
      (p.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+(1 : Mat (Fin p.extension.b)) ⊗ₖ payloadHamiltonian I))
    {z : ℕ} (t : Tester S z) : Driven.defect p t=0 := by
  have h := body_handoff_energy_balance (PhaseHardware.toEngine p hcon) t
  change energy p.bodyHamiltonian (bodyOutput p.extension t)-
    energy p.bodyHamiltonian p.extension.source.matrix+handoff p.extension t=0 at h
  unfold Driven.defect
  rw [SourceFunctional.state_sub]
  linarith

variable (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k))

local notation "q" => PhaseHardware.hardware p hD φ Hφ G hG hlocal

def raw (M : Mat (Fin (p.extension.b*D))) : Mat (Fin p.extension.b × Fin D) :=
  M.submatrix finProdFinEquiv finProdFinEquiv

def oldBodyFinal {z : ℕ} (t : Tester S z) : Mat (Fin p.extension.b) :=
  partialRight (raw p (bodyOutput (q).extension t))

def phaseFinal {z : ℕ} (t : Tester S z) : Mat (Fin D) :=
  partialLeft (raw p (bodyOutput (q).extension t))

def phaseEnergyChange {z : ℕ} (t : Tester S z) : ℝ :=
  energy Hφ.matrix (phaseFinal p hD φ Hφ G hG hlocal t)-energy Hφ.matrix φ.matrix

theorem state_energy (M : Mat (Fin (p.extension.b*D))) :
    energy (q).bodyHamiltonian M=
      energy p.bodyHamiltonian (partialRight (raw p M))+energy Hφ.matrix (partialLeft (raw p M)) := by
  rw [PhaseHardwareEnergy.physical]
  calc _ = energy (p.bodyHamiltonian ⊗ₖ (1 : Mat (Fin D))+
      (1 : Mat (Fin p.extension.b)) ⊗ₖ Hφ.matrix) (raw p M) :=
        (FactoryEnergyTransport.energy_inverse (finProdFinEquiv.symm :
          Fin (p.extension.b*D) ≃ Fin p.extension.b × Fin D) _ M).symm
       _ = _ := by rw [energy_add,energy_kron_one,energy_one_kron]

theorem source_raw : raw p (q).extension.source.matrix=p.extension.source.matrix ⊗ₖ φ.matrix := by
  change ((p.extension.source.matrix ⊗ₖ φ.matrix).submatrix
    (finProdFinEquiv.symm : Fin (p.extension.b*D) ≃ Fin p.extension.b × Fin D) finProdFinEquiv.symm).submatrix
      finProdFinEquiv finProdFinEquiv=_
  ext i j
  simp only [submatrix_apply,Equiv.symm_apply_apply]

theorem source_energy : energy (q).bodyHamiltonian (q).extension.source.matrix=
    energy p.bodyHamiltonian p.extension.source.matrix+energy Hφ.matrix φ.matrix := by
  rw [state_energy p hD φ Hφ G hG hlocal]
  calc _ = energy p.bodyHamiltonian (partialRight (p.extension.source.matrix ⊗ₖ φ.matrix))+
      energy Hφ.matrix (partialLeft (p.extension.source.matrix ⊗ₖ φ.matrix)) :=
        congrArg (fun M => energy p.bodyHamiltonian (partialRight M)+energy Hφ.matrix (partialLeft M))
          (source_raw p hD φ Hφ G hG hlocal)
       _ = _ := by rw [partialRight_kron,partialLeft_kron,φ.normalized,p.extension.source.normalized,one_smul,one_smul]

/-- Exact refund of the full nonzero phase Hamiltonian, controlled by the
original Driven defect and literal old-body/signed-handoff differences. -/
theorem exact_ledger
    (hcon : ∀ k,Conserves ((q).extension.gate k)
      ((q).bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+(1 : Mat (Fin (q).extension.b)) ⊗ₖ payloadHamiltonian I))
    {z : ℕ} (t : Tester S z) :
    phaseEnergyChange p hD φ Hφ G hG hlocal t=
      -Driven.defect p t+(handoff p.extension t-handoff (q).extension t)+
        energy p.bodyHamiltonian (bodyOutput p.extension t-oldBodyFinal p hD φ Hφ G hG hlocal t) := by
  have h0 := conserving_defect_zero q hcon t
  unfold Driven.defect at h0 ⊢
  rw [SourceFunctional.state_sub,state_energy,source_energy] at h0
  rw [SourceFunctional.state_sub,SourceFunctional.state_sub]
  change energy Hφ.matrix (partialLeft (raw p (bodyOutput (q).extension t)))-energy Hφ.matrix φ.matrix=_
  change handoff (q).extension t+
    (energy p.bodyHamiltonian (partialRight (raw p (bodyOutput (q).extension t)))+
      energy Hφ.matrix (partialLeft (raw p (bodyOutput (q).extension t)))-
        (energy p.bodyHamiltonian p.extension.source.matrix+energy Hφ.matrix φ.matrix))=0 at h0
  dsimp only [oldBodyFinal]
  linarith

end ScheduleLaw.Blueprint.PhaseEnergyRefund
