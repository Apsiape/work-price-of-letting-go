import PhaseGateDilation

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseSpectralTransport
open PhaseGateDilation
variable {a p g : Type} [Fintype a] [DecidableEq a] [Fintype p] [DecidableEq p]
    [AddCommGroup g] [DecidableEq g]

theorem conserving_back (H : Hamiltonian a) (K : Mat p) (V : Mat (a × p))
    (hV : Conserves V (diagonal (fun i => (energies H i : ℂ)) ⊗ₖ (1 : Mat p)+(1 : Mat a) ⊗ₖ K)) :
    Conserves (evolve (basis H ⊗ₖ (1 : Mat p)) V)
      (H.matrix ⊗ₖ (1 : Mat p)+(1 : Mat a) ⊗ₖ K) := by
  let W := basis H ⊗ₖ (1 : Mat p)
  let D := diagonal (fun i => (energies H i : ℂ))
  let T := D ⊗ₖ (1 : Mat p)+(1 : Mat a) ⊗ₖ K
  have hW : IsUnitary W := unitary_kron (basis_unitary H) (by constructor <;> simp)
  have hh := conjugate_conserves V W T hW hV
  have he : evolve W T=H.matrix ⊗ₖ (1 : Mat p)+(1 : Mat a) ⊗ₖ K := by
    have hadd (A B : Mat (a × p)) : evolve W (A+B)=evolve W A+evolve W B := by
      simp only [evolve,mul_add,add_mul]
    change evolve W (D ⊗ₖ (1 : Mat p)+(1 : Mat a) ⊗ₖ K)=_
    rw [hadd]
    change evolve (basis H ⊗ₖ (1 : Mat p)) (D ⊗ₖ (1 : Mat p))+
      evolve (basis H ⊗ₖ (1 : Mat p)) ((1 : Mat a) ⊗ₖ K)=_
    rw [IdleExtension.evolve_idle,IdleExtension.evolve_idle]
    have hD : evolve (basis H) D=H.matrix := H.hermitian.spectral_theorem.symm
    have h1 : evolve (basis H) (1 : Mat a)=1 := by
      simpa only [evolve,mul_one] using (basis_unitary H).2
    rw [hD,h1]
  rw [he] at hh
  exact hh

/-- The same phase Hamiltonian may carry arbitrary exact additive energy
labels for different local spectra. -/
theorem labeled_conserving (H : Hamiltonian a) (U : Mat a) (hU : IsUnitary U)
    (B : Finset g) (ω : g →+ ℝ) (l : a → g) (hl : ∀ i,ω (l i)=energies H i) :
    Conserves
      (evolve (basis H ⊗ₖ (1 : Mat ↥B)) (FinitePhaseShell.gate l B (inBasis H U)))
      (H.matrix ⊗ₖ (1 : Mat ↥B)+(1 : Mat a) ⊗ₖ diagonal (fun x : ↥B => (ω x.val : ℂ))) := by
  apply conserving_back
  have hU' : IsUnitary (inBasis H U) :=
    conjugate_unitary U _ hU (adjoint_unitary _ (basis_unitary H))
  have hs := FinitePhaseShell.conserving l B ω (inBasis H U) hU'
  simp only [hl] at hs
  rw [diagonal_total (energies H) (fun x : ↥B => ω x.val)] at hs
  exact hs

end ScheduleLaw.Blueprint.PhaseSpectralTransport
