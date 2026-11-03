import BlueprintContracts
import W2.TensorFamily
import FiniteResidueCoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint

/-- All coding registers are retained. In addition to the entropy-rate rank,
this contract bounds the logarithm of the *actual* residue dimension sublinearly.
No independence of the batch and residue is required. -/
structure SmallResidueCoding {d : ℕ} (τ : Density (Fin d)) where
  rank : ℕ → ℕ
  residue : ℕ → ℕ
  rank_pos : ∀ m, 0 < rank m
  residue_pos : ∀ m, 0 < residue m
  error : ℕ → ℝ
  error_nonneg : ∀ m, 0 ≤ error m
  error_vanishes : Vanishes error
  rank_rate : Tendsto (fun m => Real.log (rank m : ℝ)/(m+1 : ℝ))
    atTop (𝓝 (entropy τ.matrix))
  residue_rate : Tendsto (fun m => Real.log (residue m : ℝ)/(m+1 : ℝ)) atTop (𝓝 0)
  unitary : (m : ℕ) → Mat ((Fin (m+1) → Fin d) × Fin (residue m))
  projection : (m : ℕ) → Mat ((Fin (m+1) → Fin d) × Fin (residue m))
  unitary_isUnitary : ∀ m, IsUnitary (unitary m)
  projection_hermitian : ∀ m, (projection m).IsHermitian
  projection_idempotent : ∀ m, projection m * projection m = projection m
  projection_trace : ∀ m, (projection m).trace = (rank m : ℂ)
  approximation : ∀ m,
    traceDistance (partialRight (evolve (unitary m) (((rank m : ℂ)⁻¹) • projection m)))
      (tensorPower τ.matrix (m+1)) ≤ error m

/-- The missing bounded-residue spectral coding obligation. Unrestricted
purification with a residue of dimension d^(m+1)*rank m does not inhabit this type. -/
theorem small_residue_source_coding {d : ℕ} (τ : Density (Fin d)) :
    Nonempty (SmallResidueCoding τ) := by
  classical
  obtain ⟨D⟩ := FiniteResidue.typical_rounding_data τ
  have hcode (m : ℕ) := FiniteResidue.spectral_rounded_code τ m
    (D.typical m) (D.scale m) (D.scale_pos m) (D.residue m)
    (D.capacity m) (D.rank_pos m)
  choose K V P hK hKeq hV hP hPi hTr hErr using hcode
  refine ⟨{
    rank := K
    residue := D.residue
    rank_pos := hK
    residue_pos := D.residue_pos
    error := fun m => (1-∑ x ∈ D.typical m, FiniteResidue.spectralWord τ m x)
      +((D.typical m).card : ℝ)/D.scale m
    error_nonneg := D.loss_nonneg
    error_vanishes := D.loss_vanishes
    rank_rate := ?_
    residue_rate := D.residue_rate
    unitary := V
    projection := P
    unitary_isUnitary := hV
    projection_hermitian := hP
    projection_idempotent := hPi
    projection_trace := hTr
    approximation := hErr }⟩
  simpa only [hKeq] using D.rank_rate

end ScheduleLaw.Blueprint
