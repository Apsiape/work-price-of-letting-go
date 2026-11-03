import PositiveExtension

/-! The PSD cone projected onto an identity-containing Hermitian subspace
is closed. Pairing with the identity bounds the positive preimages' traces,
and hence their norms, so a convergent subsequence supplies a preimage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder InnerProductSpace RealInnerProductSpace Topology
namespace ScheduleLaw.History

def projectedPositiveCone {a : Type} [Fintype a] [DecidableEq a]
    (V : Submodule ℝ (HermitianMat a ℂ)) : Set V :=
  V.orthogonalProjection '' {A : HermitianMat a ℂ | 0 ≤ A}

theorem projection_trace_identity {a : Type} [Fintype a] [DecidableEq a]
    (V : Submodule ℝ (HermitianMat a ℂ)) (h1 : (1 : HermitianMat a ℂ) ∈ V)
    (A : HermitianMat a ℂ) :
    ⟪V.orthogonalProjection A,(⟨1,h1⟩ : V)⟫_ℝ = A.trace := by
  simpa only [HermitianMat.inner_one] using
    (Submodule.inner_orthogonalProjection_eq_of_mem_right (K := V) ⟨1,h1⟩ A)

theorem isClosed_projectedPositiveCone {a : Type} [Fintype a] [DecidableEq a]
    (V : Submodule ℝ (HermitianMat a ℂ)) (h1 : (1 : HermitianMat a ℂ) ∈ V) :
    IsClosed (projectedPositiveCone V) := by
  apply isSeqClosed_iff_isClosed.mp
  intro f z hf hz
  choose A hA hAf using hf
  have hp : Tendsto (fun n => ⟪f n,(⟨1,h1⟩ : V)⟫_ℝ) atTop
      (𝓝 ⟪z,(⟨1,h1⟩ : V)⟫_ℝ) :=
    ((continuous_id.inner continuous_const).tendsto z).comp hz
  obtain ⟨R,hR⟩ := (Metric.isBounded_range_of_tendsto _ hp).exists_norm_le
  have hnorm (n : ℕ) : ‖A n‖ ≤ R := by
    have ht : (A n).trace = ⟪f n,(⟨1,h1⟩ : V)⟫_ℝ := by
      rw [← hAf n,projection_trace_identity V h1]
    calc ‖A n‖ ≤ (A n).trace := positive_norm_le_trace _ (hA n)
      _ = ⟪f n,(⟨1,h1⟩ : V)⟫_ℝ := ht
      _ ≤ ‖⟪f n,(⟨1,h1⟩ : V)⟫_ℝ‖ := le_abs_self _
      _ ≤ R := hR _ (Set.mem_range_self n)
  obtain ⟨B,hB,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : HermitianMat a ℂ) R).tendsto_subseq
    (fun n => by simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm n)
  have hBpos : 0 ≤ B := HermitianMat.isClosed_nonneg.mem_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n => hA (φ n)))
  have hproj := (V.orthogonalProjection.continuous.tendsto B).comp hlim
  have hprojz : Tendsto (fun n => V.orthogonalProjection (A (φ n))) atTop (𝓝 z) := by
    simpa only [Function.comp_def,hAf] using hz.comp hφ.tendsto_atTop
  exact ⟨B,hBpos,tendsto_nhds_unique hproj hprojz⟩

end ScheduleLaw.History
