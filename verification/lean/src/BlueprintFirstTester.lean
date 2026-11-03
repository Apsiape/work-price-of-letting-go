import BlueprintBoundaryFormula

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def firstBoundaryTester {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0<S.visits) :
    Tester S (burstMemoryDim S) where
  initial := firstPrefixInitialVector Z hZ h
  normalized := firstPrefixInitialVector_normalized Z hZ h
  gate _ := 1
  unitary _ := ⟨by simp,by simp⟩
  gate_local k := identity_local I _ (held S k)ᶜ

theorem firstBoundaryTester_prefix {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0<S.visits) :
    prefixGram (firstInputBurst S h) (firstBoundaryTester Z hZ h)=Z (firstInputBurst S h) :=
  first_prefix_realized Z hZ h _ rfl (fun _ _ => rfl)

/-- The complete converse realization for every positive-visit schedule
with only one incoming burst. This is a subcase, not a premise for general Comb. -/
theorem one_burst_comb_realization {I : Inventory} (S : Schedule I) (h : 0<S.visits)
    [Subsingleton (InputBurst S)] (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) :
    ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t=Z b := by
  refine ⟨burstMemoryDim S,firstBoundaryTester Z hZ h,?_⟩
  intro b
  have he : b=firstInputBurst S h := Subsingleton.elim _ _
  subst b
  exact firstBoundaryTester_prefix Z hZ h

end ScheduleLaw.Blueprint
