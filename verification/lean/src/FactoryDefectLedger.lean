import FactoryPhysicalDefect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryDefectLedger
open History FactoryRegisters FactoryPhysicalHamiltonian

/-- Literal original defect of the packed Formation. All hypotheses are
local conserving-gate equations; no factory or work-law claim is assumed. -/
theorem exact_ledger {d m D R r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x4 Eg Ecode : ℝ) (e : Fin D ≃ (Fin m → Fin d) × Fin R)
    (U1 : Mat ((Fin m → Fin d) × (Fin 2 × Fin r1)))
    (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (U4 : Mat (Fin D × (Fin 2 × Fin r4)))
    (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V) (hu4 : IsUnitary U4)
    (hc1 : Conserves U1 (sumH (tensorHamiltonian (tangentHamiltonian β q) m)
      (sumH (work x1) H1.matrix)))
    (hc2 : Conserves U2 (sumH (0 : Mat (Fin D)) (sumH (work x2) H2.matrix)))
    (hc4 : Conserves U4 (sumH (0 : Mat (Fin D)) (sumH (work x4) H4.matrix))) :
    let U := circuit e U1 U2 V U4
    let hU : IsUnitary U := by convert circuit_unitary e U1 U2 V U4 hu1 hu2 hv hu4 using 1
    let F := FactoryPackedFormation.formation hd hm hD h1 h2 h4 β hβ τ q hq
      H1 H2 H4 x1 x2 (Eg-Ecode) x4 U hU
    ∀ z (t : Tester F.schedule z), Driven.defect F.hardware t=
      (energy (tensorHamiltonian (tangentHamiltonian β q) m) F.output-Ecode) +
        (Eg-energy (tensorHamiltonian (tangentHamiltonian β q) m) (partialRight
          (evolve U1 ((tensorPower q.matrix m) ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β H1))))) := by
  dsimp only
  intro z t
  rw [FactoryPhysicalDefect.registers hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4
    x1 x2 (Eg-Ecode) x4 _ _ z t]
  rw [FactoryFormedOutput.output hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4
    x1 x2 (Eg-Ecode) x4 _ _]
  exact FactoryInitializedEnergy.circuit_ledger e
    (tensorHamiltonian (tangentHamiltonian β q) m) H1.matrix H2.matrix H4.matrix x1 x2 x4 Eg Ecode
    (FactoryFormation.flat D hD) (W2.tensorFamilyDensity (fun _ : Fin m => q))
    (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
    (FactoryPackedStock.gibbsDensity h4 β H4) (FactoryFormation.flat D hD)
    U1 U2 V U4 hu1 hu2 hv hu4 hc1 hc2 hc4

end ScheduleLaw.Blueprint.FactoryDefectLedger
