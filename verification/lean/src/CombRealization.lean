import ConeConsequences

/-! The one permitted, explicitly scoped literature hypothesis for converse
realization. It states only surjectivity onto the already defined causal
prefix families, with the actual Tester and independently wired prefixGram.

Sources: Chiribella--D'Ariano--Perinotti, Phys. Rev. A 80, 022339 (2009),
Theorems 3 and 5, https://doi.org/10.1103/PhysRevA.80.022339 ;
Gutoski--Watrous, STOC 2007, pp. 565--574, Theorem 6,
https://doi.org/10.1145/1250790.1250873 .
The paper's purification/isometry construction still needs its schedule-wide
square-gate/locality assembly. No body, energy, entropy, duality, or work-law
assertion is included in this proposition. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw
namespace History

def CombRealization : Prop :=
  ∀ (I : Inventory) (S : Schedule I) (Z : PrefixMatrices S),
    IsCausalPrefixFamily S Z → ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t = Z b

def actualTesterFamilies {I : Inventory} (S : Schedule I) : Set (PrefixMatrices S) :=
  {Z | ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t = Z b}

theorem realize_causal_prefix_family (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) :
    ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t = Z b := hcomb I S Z hZ

theorem actualTesterFamilies_subset {I : Inventory} (S : Schedule I) :
    actualTesterFamilies S ⊆ {Z | IsCausalPrefixFamily S Z} := by
  rintro Z ⟨r,t,ht⟩
  have he : (fun b => prefixGram b t) = Z := funext ht
  exact he ▸ actual_causal_prefix_family S t

theorem actualTesterFamilies_eq_causal (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) : actualTesterFamilies S = {Z | IsCausalPrefixFamily S Z} := by
  apply Set.Subset.antisymm (actualTesterFamilies_subset S)
  intro Z hZ
  exact realize_causal_prefix_family hcomb S Z hZ

theorem isCompact_actualTesterFamilies (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) : IsCompact (actualTesterFamilies S) := by
  rw [actualTesterFamilies_eq_causal hcomb]
  exact isCompact_causal_prefix_set S

theorem convex_actualTesterFamilies (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) : Convex ℝ (actualTesterFamilies S) := by
  rw [actualTesterFamilies_eq_causal hcomb]
  exact causal_prefix_convex S

theorem exists_flat_tester (hcomb : CombRealization) {I : Inventory} (S : Schedule I) :
    ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t = flatPrefixFamily S b :=
  realize_causal_prefix_family hcomb S _ (flat_prefix_causal S)

theorem actual_tester_continuous_maximum (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) (f : PrefixMatrices S → ℝ) (hf : Continuous f) :
    ∃ (r : ℕ) (t : Tester S r), ∀ r' (t' : Tester S r'),
      f (fun b => prefixGram b t') ≤ f (fun b => prefixGram b t) := by
  obtain ⟨Z,hZ,hmax⟩ := causal_prefix_continuous_maximum S f hf
  obtain ⟨r,t,ht⟩ := realize_causal_prefix_family hcomb S Z hZ
  refine ⟨r,t,?_⟩
  have he : (fun b => prefixGram b t) = Z := funext ht
  rw [he]
  exact fun r' t' => hmax _ (actual_causal_prefix_family S t')

theorem actual_tester_linear_maximum (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) (L : PrefixMatrices S →L[ℝ] ℝ) :
    ∃ (r : ℕ) (t : Tester S r), ∀ r' (t' : Tester S r'),
      L (fun b => prefixGram b t') ≤ L (fun b => prefixGram b t) :=
  actual_tester_continuous_maximum hcomb S L L.continuous

end History
end ScheduleLaw
