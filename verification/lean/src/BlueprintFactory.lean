import FiniteFactoryConstruction
import W2.UniformMarginal

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Finite spectral coding: normalized rounded uniform labels with an
explicit retained residue; no independent-residue assertion is made. -/
theorem spectral_flat_coding {d : ℕ} (τ : Density (Fin d)) :
    ∃ (k r : ℕ → ℕ) (err : ℕ → ℝ), Vanishes err ∧
      Tendsto (fun m => Real.log (k m : ℝ)/(m+1 : ℝ)) atTop (𝓝 (entropy τ.matrix)) ∧
      ∀ m, 0 < k m ∧ 0 < r m ∧
        ∃ (V : Mat ((Fin (m+1) → Fin d) × Fin (r m)))
          (P : Mat ((Fin (m+1) → Fin d) × Fin (r m))),
          IsUnitary V ∧ P.IsHermitian ∧ P*P=P ∧ P.trace=(k m : ℂ) ∧
          traceDistance (partialRight (evolve V (((k m : ℂ)⁻¹) • P)))
            (tensorPower τ.matrix (m+1)) ≤ err m := by
  -- This interface leaves the retained residue dimension unrestricted.
  -- The factory still needs a separate bound on that dimension.
  classical
  obtain ⟨k,hkp,hkr⟩ := W2.entropy_rank_sequence (entropy τ.matrix) (density_entropy_nonneg τ)
  have hrep (m : ℕ) : ∃ r : ℕ,0 < r ∧
      ∃ P : Mat ((Fin (m+1) → Fin d) × Fin r),P.IsHermitian ∧ P*P=P ∧
        P.trace=(k m : ℂ) ∧ partialRight (((k m : ℂ)⁻¹) • P)=tensorPower τ.matrix (m+1) := by
    exact W2.uniform_projector_marginal
      (W2.tensorFamilyDensity (fun _ : Fin (m+1) => τ)) (k m) (hkp m)
  choose r hr P hP hPi htr hMarg using hrep
  refine ⟨k,r,fun _ => 0,tendsto_const_nhds,hkr,?_⟩
  intro m
  refine ⟨hkp m,hr m,1,P m,?_,hP m,hPi m,htr m,?_⟩
  · constructor <;> simp
  · simp only [evolve,conjTranspose_one,one_mul,mul_one,hMarg m,W2.traceDistance_self,le_refl]

/-- Energy-shell injections, exact finite full-square completion, all
thermal/failure columns and the four helper registers remain physical. -/
theorem source_factory_circuits {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef) : FactoryFamily β τ q := by
  obtain ⟨C⟩ := small_residue_source_coding τ
  exact finite_factory_of_small_residue_coding hd β hβ τ q hq C

end ScheduleLaw.Blueprint
