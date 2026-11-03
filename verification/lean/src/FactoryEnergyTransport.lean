import FactoryPreparationTransport
import FactoryPhysicalHamiltonian
import FactoryUniformBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryEnergyTransport
open History FactoryPhysicalHamiltonian

theorem norm_reindex {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (H : Mat b) : ‖H.submatrix e e‖=‖H‖ := by
  letI := matrixCStarStructure a
  letI := matrixCStarStructure b
  exact StarAlgEquiv.norm_map (matrixReindexStarEquiv e.symm) H

theorem energy_inverse {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (H : Mat b) (ρ : Mat a) :
    energy H (ρ.submatrix e.symm e.symm)=energy (H.submatrix e e) ρ := by
  have hr : (ρ.submatrix e.symm e.symm).submatrix e e=ρ := by
    ext i j
    simp only [submatrix_apply,Equiv.symm_apply_apply]
  calc _ = energy (H.submatrix e e) ((ρ.submatrix e.symm e.symm).submatrix e e) :=
        (energy_reindex e _ _).symm
       _ = _ := by rw [hr]

theorem evolve_inverse {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (U : Mat a) (ρ : Mat b) :
    (evolve (U.submatrix e.symm e.symm) ρ).submatrix e e=evolve U (ρ.submatrix e e) := by
  have hu : (U.submatrix e.symm e.symm).submatrix e e=U := by
    ext i j
    simp only [submatrix_apply,Equiv.symm_apply_apply]
  calc _ = evolve ((U.submatrix e.symm e.symm).submatrix e e) (ρ.submatrix e e) :=
        (evolve_submatrix_equiv e _ _).symm
       _ = _ := by rw [hu]

theorem preparation_conserves {b : Type} [Fintype b] [DecidableEq b] {d : ℕ}
    {β x : ℝ} {H : Hamiltonian (Fin d)} (e : b ≃ Fin d) (C : SupportConverter β H x) :
    Conserves (FactoryPreparationTransport.gate e C)
      (sumH (H.matrix.submatrix e e) (sumH (work x) C.HR.matrix)) := by
  have he : (converterHamiltonian H C.HR x).submatrix
      (FactoryPreparationTransport.frame e C.r) (FactoryPreparationTransport.frame e C.r) =
      sumH (H.matrix.submatrix e e) (sumH (work x) C.HR.matrix) := by
    ext ⟨i,w,u⟩ ⟨j,v,z⟩
    simp only [converterHamiltonian,FactoryPreparationTransport.frame,submatrix_apply,
      Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_apply,sumH,work,add_apply,
      kroneckerMap_apply,Matrix.one_apply,e.injective.eq_iff,Prod.mk.injEq]
  have hc := conserves_reindex (FactoryPreparationTransport.frame e C.r) _ _ C.conserves
  rw [he] at hc
  exact hc

theorem zero_conserves {d : ℕ} {β x : ℝ}
    (C : SupportConverter β (FiniteFlat.zeroHamiltonian d) x) :
    Conserves C.U (sumH (0 : Mat (Fin d)) (sumH (work x) C.HR.matrix)) := C.conserves

theorem preparation_error {b : Type} [Fintype b] [DecidableEq b] {d : ℕ}
    (e : b ≃ Fin d) (U : Mat (Fin d)) (hU : IsUnitary U) (E : Fin d → ℝ) (i : Fin d)
    (ρ : Density b) (M ε : ℝ) (hM : 0 ≤ M)
    (hn : ‖evolve U (diagonal (fun j => (E j : ℂ)))‖ ≤ M)
    (hp : 1-ε ≤ energy ((FactorySupport.eigenProjection U i).submatrix e e) ρ.matrix) :
    |energy ((evolve U (diagonal (fun j => (E j : ℂ)))).submatrix e e) ρ.matrix-E i| ≤ 2*M*ε := by
  let σ : Density (Fin d) := FactoryPreparationTransport.density e ρ
  have hs : 1-ε ≤ energy (FactorySupport.eigenProjection U i) σ.matrix := by
    rw [show σ.matrix=ρ.matrix.submatrix e.symm e.symm from rfl,energy_inverse]
    exact hp
  have hgap (j : Fin d) : |E j-E i| ≤ 2*M :=
    (FactoryUniformBounds.spectral_gap U hU E i j).trans (by linarith)
  have hb := FactoryPreparedEnergy.preparation_error U hU E i σ (2*M) ε (by positivity) hgap hs
  rw [show σ.matrix=ρ.matrix.submatrix e.symm e.symm from rfl,energy_inverse] at hb
  exact hb

end ScheduleLaw.Blueprint.FactoryEnergyTransport
