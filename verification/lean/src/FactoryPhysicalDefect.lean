import FactoryInitializedEnergy
import FactoryFormedOutput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPhysicalDefect
open History FactoryRegisters FactoryRegisterOutput FactoryPhysicalHamiltonian

theorem source_in_frame {I : Inventory} {S : Schedule I} {β : ℝ} (p : Driven S β)
    {a : Type} [Fintype a] [DecidableEq a] (e : a ≃ Fin p.c × (Fin p.w × Fin p.r)) :
    p.extension.source.matrix.submatrix (e.trans p.split.symm) (e.trans p.split.symm) =
      (p.controller.matrix ⊗ₖ (pureMatrix (fun j => if j=p.initialLevel then 1 else 0) ⊗ₖ
        gibbs β p.HR)).submatrix e e := by
  rw [p.source_product]
  ext i j
  change (p.controller.matrix ⊗ₖ (pureMatrix (fun j => if j=p.initialLevel then 1 else 0) ⊗ₖ
    gibbs β p.HR)) (p.split (p.split.symm (e i))) (p.split (p.split.symm (e j))) = _
  rw [p.split.apply_symm_apply,p.split.apply_symm_apply]
  rfl

theorem defect_in_frame {I : Inventory} {S : Schedule I} {β : ℝ}
    (p : Driven S β) (hS : S.visits=0) {a : Type} [Fintype a] [DecidableEq a]
    (e : a ≃ Fin p.extension.b) (H U ρ : Mat a)
    (hh : p.bodyHamiltonian.submatrix e e=H)
    (hi : p.extension.source.matrix.submatrix e e=ρ)
    {z : ℕ} (t : Tester S z)
    (ho : (bodyOutput p.extension t).submatrix e e=evolve U ρ) :
    Driven.defect p t=energy H (evolve U ρ)-energy H ρ := by
  unfold Driven.defect
  rw [handoff_zero_visits p.extension hS t,zero_add]
  have he : energy p.bodyHamiltonian (bodyOutput p.extension t-p.extension.source.matrix)=
      energy p.bodyHamiltonian (bodyOutput p.extension t)-energy p.bodyHamiltonian p.extension.source.matrix := by
    simp only [energy,mul_sub,trace_sub,Complex.sub_re]
  rw [he,← energy_reindex e,← energy_reindex e,hh,hi,ho]

/-- The original Formation defect is exactly the energy change of its literal
full physical circuit, for every coherent tester. -/
theorem registers {d m D r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β ≠ 0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) :
    let F := FactoryPackedFormation.formation hd hm hD h1 h2 h4 β hβ τ q hq
      H1 H2 H4 x1 x2 x3 x4 U hU
    let K := hamiltonian (tensorHamiltonian (tangentHamiltonian β q) m)
      H1.matrix H2.matrix H4.matrix x1 x2 x3 x4
    let ρ := FactoryInitializer.matrix (FactoryFormation.flat D hD)
      (W2.tensorFamilyDensity (fun _ : Fin m => q))
      (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
      (FactoryPackedStock.gibbsDensity h4 β H4) (FactoryFormation.flat D hD)
    ∀ z (t : Tester F.schedule z), Driven.defect F.hardware t=energy K (evolve U ρ)-energy K ρ := by
  dsimp only
  intro z t
  let F := FactoryPackedFormation.formation hd hm hD h1 h2 h4 β hβ τ q hq
    H1 H2 H4 x1 x2 x3 x4 U hU
  let J := FactoryPacking.frame d m D r1 r2 r4
  let E := J.trans F.hardware.split.symm
  let ρ := FactoryInitializer.matrix (FactoryFormation.flat D hD)
    (W2.tensorFamilyDensity (fun _ : Fin m => q))
    (FactoryPackedStock.gibbsDensity h1 β H1) (FactoryPackedStock.gibbsDensity h2 β H2)
    (FactoryPackedStock.gibbsDensity h4 β H4) (FactoryFormation.flat D hD)
  have hi : F.hardware.extension.source.matrix.submatrix E E=ρ := by
    rw [source_in_frame F.hardware J]
    exact FactoryPackedStock.initialized_registers hD h1 h2 h4 β hβ q hq m H1 H2 H4
  have ho : (bodyOutput F.hardware.extension t).submatrix E E=evolve U ρ := by
    letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    let A := FactoryPacking.auxSize D r1 r2 r4
    have hA : 0 < A := FactoryPackedFormation.auxiliary_pos hD h1 h2 h4
    have hR : 0 < (Fintype.card (Fin m → Fin d))*A := Nat.mul_pos Fintype.card_pos hA
    let HR := FactoryFormation.reservoir (m:=m) β q (FactoryPacking.auxHamiltonian (D:=D) H1 H2 H4)
    have hb : (bodyOutput F.hardware.extension t).submatrix F.hardware.split.symm F.hardware.split.symm =
        evolve (U.submatrix J.symm J.symm)
          ((FactoryFormation.flat D hD).matrix ⊗ₖ (FactoryPackedStock.basis FactoryPacking.initial ⊗ₖ gibbs β HR)) :=
      FactoryDriven.output FactoryFormation.schedule rfl β D 16
        ((Fintype.card (Fin m → Fin d))*A) hD (by decide) hR
        (FactoryFormation.flat D hD) (FiniteFlat.zeroHamiltonian D) HR
        (FactoryPacking.workEnergy x1 x2 x3 x4) FactoryPacking.initial FactoryPacking.nominal
        0 _ (unitary_submatrix _ hU) t
    change ((bodyOutput F.hardware.extension t).submatrix F.hardware.split.symm F.hardware.split.symm).submatrix J J=_
    rw [hb]
    have hu : (U.submatrix J.symm J.symm).submatrix J J=U := by
      ext i j
      simp only [submatrix_apply,Equiv.symm_apply_apply]
    calc
      _ = evolve ((U.submatrix J.symm J.symm).submatrix J J)
          (((FactoryFormation.flat D hD).matrix ⊗ₖ
            (FactoryPackedStock.basis FactoryPacking.initial ⊗ₖ gibbs β HR)).submatrix J J) :=
        (evolve_submatrix_equiv J _ _).symm
      _ = evolve U ρ := by
        rw [hu]
        congr 1
        exact FactoryPackedStock.initialized_registers hD h1 h2 h4 β hβ q hq m H1 H2 H4
  exact defect_in_frame F.hardware F.empty E _ U ρ
    (packed hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU) hi t ho

end ScheduleLaw.Blueprint.FactoryPhysicalDefect

