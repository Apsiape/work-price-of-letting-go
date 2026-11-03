import BlueprintBellSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem released_subset_arrived {I : Inventory} (S : Schedule I) (n : ℕ) :
    released S n ⊆ arrived S n := by
  intro v hv
  have ho := S.ordered v
  simp only [released,arrived,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
  change (S.position (v,false)).val < (S.position (v,true)).val at ho
  omega

def prefixLive {I : Inventory} {S : Schedule I} (b : InputBurst S) : Finset (Fin S.visits) :=
  activeVisits S (prefixCut b)

theorem prefixLive_eq {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    prefixLive b=arrived S (recordTime b) \ released S (recordTime b) := by
  ext v
  simp only [prefixLive,activeVisits,arrived,released,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_univ,true_and,prefixCut,recordTime]
  omega

theorem prefixLive_unreleased {I : Inventory} {S : Schedule I} (b : InputBurst S)
    {v : Fin S.visits} (hv : v∈prefixLive b) : v∈(released S (recordTime b))ᶜ := by
  rw [prefixLive_eq] at hv
  exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2

theorem prefixFuture_unreleased {I : Inventory} {S : Schedule I} (b : InputBurst S)
    {v : Fin S.visits} (hv : v∈(arrived S (recordTime b))ᶜ) :
    v∈(released S (recordTime b))ᶜ :=
  Finset.mem_compl.mpr (fun ho => Finset.mem_compl.mp hv (released_subset_arrived S _ ho))

def prefixTailInputs {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (u : Registers S (released S (recordTime b))ᶜ) : Registers S (arrived S (recordTime b))ᶜ :=
  fun v => u ⟨v.val,prefixFuture_unreleased b v.property⟩

def prefixTailPayload {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (u : Registers S (released S (recordTime b))ᶜ) : Payload I :=
  (visitPayloadPartition S (prefixLive b)
    (activeVisits_carriers_injective S (prefixCut b) _ (Finset.Subset.refl _))).symm
      (fun v => u ⟨v.val,prefixLive_unreleased b v.property⟩,fun c => ⟨0,I.dim_pos c.val⟩)

def canonicalEnvironmentEmbedding {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    (PrefixSpace b × Registers S (released S (recordTime b))ᶜ) ↪
      (Record S (arrived S (recordTime b))ᶜ (released S (recordTime b))ᶜ ×
        (Payload I × Fin (burstMemoryDim S))) where
  toFun q := ((prefixTailInputs b q.2,q.2),(prefixTailPayload b q.2,canonicalMemoryEmbedding b q.1))
  inj' := by
    intro q r h
    have hu : q.2=r.2 := congrArg (fun x => x.1.2) h
    have hm : q.1=r.1 := (canonicalMemoryEmbedding b).injective (congrArg (fun x => x.2.2) h)
    exact Prod.ext hm hu

def canonicalEnvironmentMatrix {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  registerEmbedding (canonicalEnvironmentEmbedding b)

theorem canonicalEnvironmentMatrix_isometry {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    (canonicalEnvironmentMatrix b)ᴴ*canonicalEnvironmentMatrix b=1 := registerEmbedding_isometry _

def canonicalPrefixVector {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (x : Raw S (burstMemoryDim S)) : ℂ :=
  ∑ q : PrefixSpace b × Registers S (released S (recordTime b))ᶜ,
    prefixPurification S Z hZ b ((recordCoordinates S _ _ _ x).1,q.1)*
      canonicalEnvironmentMatrix b ((recordCoordinates S _ _ _ x).2) q

theorem canonicalPrefixVector_coordinates {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (x : PrefixSpace b)
    (y : Record S (arrived S (recordTime b))ᶜ (released S (recordTime b))ᶜ ×
      (Payload I × Fin (burstMemoryDim S))) :
    canonicalPrefixVector Z hZ b ((recordCoordinates S _ _ _).symm (x,y))=
      ∑ q : PrefixSpace b × Registers S (released S (recordTime b))ᶜ,
        prefixPurification S Z hZ b (x,q.1)*canonicalEnvironmentMatrix b y q := by
  simp only [canonicalPrefixVector,Equiv.apply_symm_apply]

theorem canonicalPrefixVector_gram {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) :
    partialRight (pureMatrix (fun x => canonicalPrefixVector Z hZ b
      ((recordCoordinates S _ _ _).symm x))) =
      (Fintype.card (Registers S (released S (recordTime b))ᶜ):ℂ) • Z b := by
  simp only [canonicalPrefixVector,Equiv.apply_symm_apply]
  rw [copied_environment_gram _ _ (canonicalEnvironmentMatrix_isometry b),prefixPurification_gram]

theorem prefixGram_of_canonical_vector {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (t : Tester S (burstMemoryDim S))
    (b : InputBurst S)
    (h : amplitudes t (allBellSource S) (recordTime b)=canonicalPrefixVector Z hZ b) :
    prefixGram b t=Z b := by
  apply prefixGram_of_allBellGram
  unfold allBellGram
  rw [h]
  exact canonicalPrefixVector_gram Z hZ b

theorem canonicalPrefixVector_at_environment {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (x m : PrefixSpace b) (u : Registers S (released S (recordTime b))ᶜ) :
    canonicalPrefixVector Z hZ b
      ((recordCoordinates S _ _ _).symm (x,canonicalEnvironmentEmbedding b (m,u)))=
      prefixPurification S Z hZ b (x,m) := by
  classical
  rw [canonicalPrefixVector_coordinates]
  simp [canonicalEnvironmentMatrix,registerEmbedding,(canonicalEnvironmentEmbedding b).injective.eq_iff]

end ScheduleLaw.Blueprint
