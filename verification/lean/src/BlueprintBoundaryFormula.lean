import BlueprintFirstBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem prefixTailPayload_live {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (u : Registers S (released S (recordTime b))ᶜ) (v : {v // v∈prefixLive b}) :
    prefixTailPayload b u (S.carrier v.val)=u ⟨v.val,prefixLive_unreleased b v.property⟩ := by
  have he := (visitPayloadPartition S (prefixLive b)
    (activeVisits_carriers_injective S (prefixCut b) _ (Finset.Subset.refl _))).apply_symm_apply
      (fun v => u ⟨v.val,prefixLive_unreleased b v.property⟩,fun c => ⟨0,I.dim_pos c.val⟩)
  exact congrArg (fun p => p.1 v) he

theorem prefixTailPayload_zero {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (u : Registers S (released S (recordTime b))ᶜ)
    (c : {c // c∈(visitCarriers S (prefixLive b))ᶜ}) :
    prefixTailPayload b u c.val=⟨0,I.dim_pos c.val⟩ := by
  have he := (visitPayloadPartition S (prefixLive b)
    (activeVisits_carriers_injective S (prefixCut b) _ (Finset.Subset.refl _))).apply_symm_apply
      (fun v => u ⟨v.val,prefixLive_unreleased b v.property⟩,fun c => ⟨0,I.dim_pos c.val⟩)
  exact congrArg (fun p => p.2 c) he

theorem prefixTailPayload_eq_iff {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (u : Registers S (released S (recordTime b))ᶜ) (p : Payload I) :
    p=prefixTailPayload b u ↔
      (∀ v : {v // v∈prefixLive b}, p (S.carrier v.val)=u ⟨v.val,prefixLive_unreleased b v.property⟩) ∧
      (∀ c : {c // c∈(visitCarriers S (prefixLive b))ᶜ}, p c.val=⟨0,I.dim_pos c.val⟩) := by
  constructor
  · intro h
    subst p
    exact ⟨prefixTailPayload_live b u,prefixTailPayload_zero b u⟩
  · rintro ⟨hl,hz⟩
    apply (visitPayloadPartition S (prefixLive b)
      (activeVisits_carriers_injective S (prefixCut b) _ (Finset.Subset.refl _))).injective
    rw [prefixTailPayload,Equiv.apply_symm_apply]
    apply Prod.ext
    · exact funext hl
    · exact funext hz

def canonicalRecordAmplitude {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (x : PrefixSpace b) (m : Fin (burstMemoryDim S)) : ℂ :=
  ∑ q : PrefixSpace b, prefixPurification S Z hZ b (x,q)*
    (if m=canonicalMemoryEmbedding b q then 1 else 0)

theorem canonical_environment_sum {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (x : PrefixSpace b) (a : Registers S (arrived S (recordTime b))ᶜ)
    (u : Registers S (released S (recordTime b))ᶜ) (p : Payload I) (m : Fin (burstMemoryDim S)) :
    (∑ q : PrefixSpace b × Registers S (released S (recordTime b))ᶜ,
      prefixPurification S Z hZ b (x,q.1)*canonicalEnvironmentMatrix b ((a,u),(p,m)) q)=
      if a=prefixTailInputs b u ∧ p=prefixTailPayload b u then canonicalRecordAmplitude Z hZ b x m else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  have hs (q : PrefixSpace b) :
      (∑ v : Registers S (released S (recordTime b))ᶜ,
        prefixPurification S Z hZ b (x,q)*canonicalEnvironmentMatrix b ((a,u),(p,m)) (q,v))=
      prefixPurification S Z hZ b (x,q)*canonicalEnvironmentMatrix b ((a,u),(p,m)) (q,u) := by
    apply Finset.sum_eq_single u
    · intro v _ hv
      have hn : ((a,u),(p,m))≠canonicalEnvironmentEmbedding b (q,v) := by
        intro he
        exact hv (congrArg (fun y => y.1.2) he).symm
      simp only [canonicalEnvironmentMatrix,registerEmbedding,if_neg hn,mul_zero]
    · simp
  simp_rw [hs]
  by_cases ha : a=prefixTailInputs b u <;> by_cases hp : p=prefixTailPayload b u <;>
    simp [canonicalEnvironmentMatrix,registerEmbedding,canonicalEnvironmentEmbedding,
      Prod.mk.injEq,ha,hp,canonicalRecordAmplitude]

def canonicalBoundaryCoordinates {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  recordCoordinates S (burstMemoryDim S) (arrived S (recordTime b)) (released S (recordTime b))

theorem canonicalPrefixVector_formula {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (x : Raw S (burstMemoryDim S)) :
    canonicalPrefixVector Z hZ b x=
      if (canonicalBoundaryCoordinates b x).2.1.1=prefixTailInputs b (canonicalBoundaryCoordinates b x).2.1.2 ∧
          x.2.1=prefixTailPayload b (canonicalBoundaryCoordinates b x).2.1.2 then
        canonicalRecordAmplitude Z hZ b (canonicalBoundaryCoordinates b x).1 x.2.2 else 0 := by
  exact canonical_environment_sum Z hZ b (canonicalBoundaryCoordinates b x).1
    (canonicalBoundaryCoordinates b x).2.1.1 (canonicalBoundaryCoordinates b x).2.1.2 x.2.1 x.2.2

end ScheduleLaw.Blueprint
