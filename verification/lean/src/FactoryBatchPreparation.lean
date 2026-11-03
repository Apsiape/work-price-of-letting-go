import FactoryBatchSpectrum
import FactoryPackedStock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryBatchPreparation
open History FactoryPhysicalHamiltonian

theorem dimension_pos {d : ℕ} (hd : 0 < d) (m : ℕ) : 0 < Fintype.card (Fin m → Fin d) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact Fintype.card_pos

def eigenIndex {d : ℕ} (hd : 0 < d) (m : ℕ) : Fin (Fintype.card (Fin m → Fin d)) :=
  ⟨0,dimension_pos hd m⟩

def eigenEnergy {d : ℕ} (hd : 0 < d) (β : ℝ) (q : Density (Fin d)) (m : ℕ) : ℝ :=
  (FactoryBatchSpectrum.hamiltonian β q m).hermitian.eigenvalues (eigenIndex hd m)

def projection {d : ℕ} (hd : 0 < d) (β : ℝ) (q : Density (Fin d)) (m : ℕ) : Mat (Fin m → Fin d) :=
  (FactorySupport.eigenProjection (FactoryBatchSpectrum.hamiltonian β q m).hermitian.eigenvectorUnitary
    (eigenIndex hd m)).submatrix (FactoryBatchSpectrum.index d m) (FactoryBatchSpectrum.index d m)

theorem projection_hermitian {d : ℕ} (hd : 0 < d) (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    (projection hd β q m).IsHermitian :=
  (FactoryPreparationBounds.eigen_hermitian _ _).submatrix _

theorem projection_idempotent {d : ℕ} (hd : 0 < d) (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    projection hd β q m*projection hd β q m=projection hd β q m := by
  have hu : IsUnitary ((FactoryBatchSpectrum.hamiltonian β q m).hermitian.eigenvectorUnitary :
      Mat (Fin (Fintype.card (Fin m → Fin d)))) := by
    convert (FactoryBatchSpectrum.hamiltonian β q m).hermitian.eigenvectorUnitary.property using 1
  have hi := FactoryPreparationBounds.eigen_idempotent _ hu (eigenIndex hd m)
  have hs := congrArg (fun M => M.submatrix (FactoryBatchSpectrum.index d m) (FactoryBatchSpectrum.index d m)) hi
  unfold projection
  exact (submatrix_mul_equiv _ _ (FactoryBatchSpectrum.index d m)
    (FactoryBatchSpectrum.index d m) (FactoryBatchSpectrum.index d m)).trans hs

theorem projection_trace {d : ℕ} (hd : 0 < d) (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    (projection hd β q m).trace=1 := by
  rw [projection,submatrix_trace_equiv]
  apply FactoryPreparationBounds.eigen_trace
  convert (FactoryBatchSpectrum.hamiltonian β q m).hermitian.eigenvectorUnitary.property using 1

theorem eigen_bound {d : ℕ} (hd : 0 < d) (β : ℝ) (q : Density (Fin d)) (m : ℕ) :
    |eigenEnergy hd β q m| ≤ (m : ℝ)*
      (∑ i,|(FactoryGibbs.tangent β q).hermitian.eigenvalues i|) := by
  let H := FactoryBatchSpectrum.hamiltonian β q m
  let U : Mat (Fin (Fintype.card (Fin m → Fin d))) := H.hermitian.eigenvectorUnitary
  have hu : IsUnitary U := by convert H.hermitian.eigenvectorUnitary.property using 1
  have hH : H.matrix=evolve U (diagonal (fun j => (H.hermitian.eigenvalues j : ℂ))) := H.hermitian.spectral_theorem
  have hb := FactoryUniformBounds.eigenvalue_abs U hu H.hermitian.eigenvalues (eigenIndex hd m)
  rw [← hH] at hb
  exact hb.trans (FactoryBatchSpectrum.norm_bound β q m)

/-- One actually constructed batch preparation provides local success,
the fixed eigenprojection support, exact conservation and its energy error. -/
theorem prepare {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β) (q : Density (Fin d))
    (hq : q.matrix.PosDef) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : SupportConverter β (FactoryBatchSpectrum.hamiltonian β q m)
      (-eigenEnergy hd β q m-1),
      let U := FactoryPreparationTransport.gate (FactoryBatchSpectrum.index d m) C
      Conserves U (sumH (tensorHamiltonian (tangentHamiltonian β q) m)
        (sumH (work (-eigenEnergy hd β q m-1)) C.HR.matrix)) ∧
      ∀ ρ : Density (Fin m → Fin d),
        1-ε ≤ energy ((1 : Mat (Fin m → Fin d)) ⊗ₖ
          (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
          (evolve U (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR))) ∧
        1-ε ≤ energy (projection hd β q m) (partialRight
          (evolve U (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)))) ∧
        |eigenEnergy hd β q m-energy (tensorHamiltonian (tangentHamiltonian β q) m)
          (partialRight (evolve U (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR))))| ≤
          2*((m : ℝ)*(∑ i,|(FactoryGibbs.tangent β q).hermitian.eigenvalues i|))*ε := by
  let H := FactoryBatchSpectrum.hamiltonian β q m
  let U : Mat (Fin (Fintype.card (Fin m → Fin d))) := H.hermitian.eigenvectorUnitary
  let E := H.hermitian.eigenvalues
  let i := eigenIndex hd m
  have hu : IsUnitary U := by convert H.hermitian.eigenvectorUnitary.property using 1
  have hH : H.matrix=evolve U (diagonal (fun j => (E j : ℂ))) := H.hermitian.spectral_theorem
  have hp : partition β H=1 := FactoryBatchSpectrum.partition_one β hβ.ne' q hq m
  have hex := FactoryPreparationTransport.prepare (FactoryBatchSpectrum.index d m)
    (dimension_pos hd m) β hβ H U hu E hH i ε hε
  rw [hp,Real.log_one,zero_div,sub_zero] at hex
  obtain ⟨C,hC⟩ := hex
  refine ⟨C,?_,?_⟩
  · have hc := FactoryEnergyTransport.preparation_conserves (FactoryBatchSpectrum.index d m) C
    rw [FactoryBatchSpectrum.physical] at hc
    exact hc
  intro ρ
  obtain ⟨hw,hs⟩ := hC ρ
  refine ⟨hw,hs,?_⟩
  let γ := FactoryPackedStock.gibbsDensity C.r_pos β C.HR
  let W := FactoryPreparationTransport.gate (FactoryBatchSpectrum.index d m) C
  have hW : IsUnitary W := FactoryPreparationTransport.unitary _ C
  let S := evolve W (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ.matrix))
  have hS : S.PosSemidef :=
    (ρ.positive.kronecker ((pureMatrix_positive _).kronecker γ.positive)).mul_mul_conjTranspose_same W
  have ht : S.trace=1 := evolve_trace_one _ _ hW (by
    simp only [trace_kronecker,ρ.normalized,SupportRun.level_trace,γ.normalized,one_mul])
  let σ : Density (Fin m → Fin d) := ⟨partialRight S,partialRight_positive hS,by rw [partialRight_trace,ht]⟩
  let M : ℝ := (m : ℝ)*(∑ j,|(FactoryGibbs.tangent β q).hermitian.eigenvalues j|)
  have hn : ‖evolve U (diagonal (fun j => (E j : ℂ)))‖ ≤ M := by
    rw [← hH]
    exact FactoryBatchSpectrum.norm_bound β q m
  have hb := FactoryEnergyTransport.preparation_error (FactoryBatchSpectrum.index d m)
    U hu E i σ M ε (by dsimp [M]; positivity) hn hs
  rw [← hH,FactoryBatchSpectrum.physical] at hb
  simpa only [abs_sub_comm] using hb

end ScheduleLaw.Blueprint.FactoryBatchPreparation

