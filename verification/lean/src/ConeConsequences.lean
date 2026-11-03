import FlatPrefixes

/-! Norm normalization and attainment on the abstract prefix feasible set.
Attainment by an actual tester still requires the unproved realization map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw
namespace History

theorem causal_prefix_traceNorm {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) :
    Matrix.traceNorm (Z b) = (prefixDimension b : ℝ) := by
  have he : ((Matrix.traceNorm (Z b) : ℝ) : ℂ) = (prefixDimension b : ℂ) :=
    (hZ.1 b).traceNorm_eq_trace.trans (causal_prefix_trace S Z hZ b)
  exact_mod_cast he

theorem causal_prefix_continuous_maximum {I : Inventory} (S : Schedule I)
    (f : PrefixMatrices S → ℝ) (hf : Continuous f) :
    ∃ Z : PrefixMatrices S, IsCausalPrefixFamily S Z ∧
      ∀ W : PrefixMatrices S, IsCausalPrefixFamily S W → f W ≤ f Z := by
  obtain ⟨Z,hZ,hmax⟩ := (isCompact_causal_prefix_set S).exists_isMaxOn
    (causal_prefix_set_nonempty S) hf.continuousOn
  exact ⟨Z,hZ,fun W hW => hmax hW⟩

theorem causal_prefix_linear_maximum {I : Inventory} (S : Schedule I)
    (L : PrefixMatrices S →L[ℝ] ℝ) :
    ∃ Z : PrefixMatrices S, IsCausalPrefixFamily S Z ∧
      ∀ W : PrefixMatrices S, IsCausalPrefixFamily S W → L W ≤ L Z :=
  causal_prefix_continuous_maximum S L L.continuous

theorem actual_testers_bounded_by_prefix_maximum {I : Inventory} (S : Schedule I)
    (L : PrefixMatrices S →L[ℝ] ℝ) :
    ∃ Z : PrefixMatrices S, IsCausalPrefixFamily S Z ∧
      ∀ r (t : Tester S r), L (fun b => prefixGram b t) ≤ L Z := by
  obtain ⟨Z,hZ,hmax⟩ := causal_prefix_linear_maximum S L
  exact ⟨Z,hZ,fun r t => hmax _ (actual_causal_prefix_family S t)⟩

end History
end ScheduleLaw
