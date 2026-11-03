import FactoryPackedFormation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFormedOutput
open History FactoryPacking FactoryPackedStock FactoryPackedFormation FactoryRegisterOutput

/-- Output of the unchanged Formation contract for the physical register
unitary, evaluated in the exact original Gibbs initializer. -/
theorem output {d m D r1 r2 r4 : ℕ} (hd : 0<d) (hm : 0 < m) (hD : 0<D)
    (h1 : 0<r1) (h2 : 0<r2) (h4 : 0<r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (FactoryRegisters.Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) :
    (formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU).output =
      marginal batchFrame (evolve U
        (FactoryInitializer.matrix (FactoryFormation.flat D hD)
          (W2.tensorFamilyDensity (fun _ : Fin m => q))
          (gibbsDensity h1 β H1) (gibbsDensity h2 β H2) (gibbsDensity h4 β H4)
          (FactoryFormation.flat D hD))) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let A := auxSize D r1 r2 r4
  have hA : 0<A := auxiliary_pos hD h1 h2 h4
  have hR : 0<(Fintype.card (Fin m → Fin d))*A := Nat.mul_pos Fintype.card_pos hA
  let HR := FactoryFormation.reservoir (m:=m) β q (auxHamiltonian (D:=D) H1 H2 H4)
  let J := frame d m D r1 r2 r4
  let source := (FactoryFormation.flat D hD).matrix ⊗ₖ (basis initial ⊗ₖ gibbs β HR)
  let input := FactoryInitializer.matrix (FactoryFormation.flat D hD)
    (W2.tensorFamilyDensity (fun _ : Fin m => q))
    (gibbsDensity h1 β H1) (gibbsDensity h2 β H2) (gibbsDensity h4 β H4)
    (FactoryFormation.flat D hD)
  have hs : source=input.submatrix J.symm J.symm := by
    have he := initialized_registers hD h1 h2 h4 β hβ q hq m H1 H2 H4
    ext i j
    have hh := congrArg (fun M => M (J.symm i) (J.symm j)) he
    simpa only [submatrix_apply,J,Equiv.apply_symm_apply,source,HR,input] using hh
  let F := formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU
  have hb : (bodyOutput F.hardware.extension (idleTester FactoryFormation.schedule)).submatrix
      F.hardware.split.symm F.hardware.split.symm =
      evolve (U.submatrix J.symm J.symm) source :=
    FactoryDriven.output FactoryFormation.schedule rfl β D 16
      ((Fintype.card (Fin m → Fin d))*A) hD (by decide) hR
      (FactoryFormation.flat D hD) (FiniteFlat.zeroHamiltonian D) HR
      (workEnergy x1 x2 x3 x4) initial nominal 0 _ (unitary_submatrix _ hU)
      (idleTester FactoryFormation.schedule)
  change partialRight ((partialLeft (partialLeft
    ((bodyOutput F.hardware.extension (idleTester FactoryFormation.schedule)).submatrix
      F.hardware.split.symm F.hardware.split.symm))).submatrix
        (FactoryFormation.reservoirSplit d m A).symm
        (FactoryFormation.reservoirSplit d m A).symm)=_
  rw [hb,hs,evolve_submatrix_equiv]
  rw [reservoir_batch (FactoryFormation.reservoirSplit d m A)
    ((evolve U input).submatrix J.symm J.symm)]
  exact packed_batch (evolve U input)

end ScheduleLaw.Blueprint.FactoryFormedOutput
