import FactoryPackedFormation
import FactoryControllerReturn
import FactoryResetCircuit
import FactoryReturnPacking
import FactoryDrivenProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPackedReturn
open History FactoryPacking FactoryPackedFormation FactoryRegisters

theorem whole_product {d m D r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ) {r : Type} [Fintype r] [DecidableEq r]
    (e : Fin D ≃ (Fin m → Fin d) × r)
    (U1 : Mat ((Fin m → Fin d) × (Fin 2 × Fin r1)))
    (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (U4 : Mat (Fin D × (Fin 2 × Fin r4)))
    (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V) (hu4 : IsUnitary U4) :
    let U := circuit e U1 U2 V U4
    let hU : IsUnitary U := by convert circuit_unitary e U1 U2 V U4 hu1 hu2 hv hu4 using 1
    let F := formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU
    ∀ z (t : Tester F.schedule z),
      ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin z)),
        FactoryControllerReturn.wholeState F.hardware t = F.hardware.controller.matrix ⊗ₖ σ.matrix := by
  dsimp only
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let A := auxSize D r1 r2 r4
  have hA : 0 < A := auxiliary_pos hD h1 h2 h4
  have hR : 0 < (Fintype.card (Fin m → Fin d))*A := Nat.mul_pos Fintype.card_pos hA
  let HR := FactoryFormation.reservoir (m:=m) β q (auxHamiltonian (D:=D) H1 H2 H4)
  let J := FactoryPacking.frame d m D r1 r2 r4
  let U := circuit e U1 U2 V U4
  have hU : IsUnitary U := by convert circuit_unitary e U1 U2 V U4 hu1 hu2 hv hu4 using 1
  let source := (FactoryFormation.flat D hD).matrix ⊗ₖ (FactoryPackedStock.basis initial ⊗ₖ gibbs β HR)
  let input := FactoryInitializer.matrix (FactoryFormation.flat D hD)
    (W2.tensorFamilyDensity (fun _ : Fin m => q))
    (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
    (FactoryPackedStock.gibbsDensity h4 β H4) (FactoryFormation.flat D hD)
  obtain ⟨ω,hω⟩ := FactoryReturnPacking.packed_return hD
    (W2.tensorFamilyDensity (fun _ : Fin m => q))
    (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
    (FactoryPackedStock.gibbsDensity h4 β H4) e U1 U2 V U4 hu1 hu2 hv hu4
  have hs : source=input.submatrix J.symm J.symm := by
    have he := FactoryPackedStock.initialized_registers hD h1 h2 h4 β hβ q hq m H1 H2 H4
    ext i j
    have hh := congrArg (fun M => M (J.symm i) (J.symm j)) he
    simpa only [submatrix_apply,J,Equiv.apply_symm_apply,source,HR,input] using hh
  have hout : evolve (U.submatrix J.symm J.symm) source =
      (FactoryFormation.flat D hD).matrix ⊗ₖ ω.matrix := by
    rw [hs,evolve_submatrix_equiv]
    exact hω
  intro z t
  exact FactoryDrivenProduct.product FactoryFormation.schedule rfl β D 16
    ((Fintype.card (Fin m → Fin d))*A) hD (by decide) hR
    (FactoryFormation.flat D hD) (FiniteFlat.zeroHamiltonian D) HR
    (workEnergy x1 x2 x3 x4) initial nominal 0 _
    (unitary_submatrix _ hU) ω hout t

theorem exact_returns {d m D r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ) {r : Type} [Fintype r] [DecidableEq r]
    (e : Fin D ≃ (Fin m → Fin d) × r)
    (U1 : Mat ((Fin m → Fin d) × (Fin 2 × Fin r1)))
    (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (U4 : Mat (Fin D × (Fin 2 × Fin r4)))
    (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V) (hu4 : IsUnitary U4) :
    let U := circuit e U1 U2 V U4
    let hU : IsUnitary U := by convert circuit_unitary e U1 U2 V U4 hu1 hu2 hv hu4 using 1
    let F := formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU
    ∀ z (t : Tester F.schedule z),
      Driven.controllerProductDefect F.hardware t=0 ∧
        Driven.controllerEnergyChange F.hardware t=0 ∧
          Driven.controllerEntropyChange F.hardware t=0 := by
  dsimp only
  intro z t
  obtain ⟨σ,hσ⟩ := whole_product hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4
    x1 x2 x3 x4 e U1 U2 V U4 hu1 hu2 hv hu4 z t
  exact FactoryControllerReturn.exact_returns _ t σ hσ

end ScheduleLaw.Blueprint.FactoryPackedReturn
