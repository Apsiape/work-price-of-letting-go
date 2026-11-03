import BlueprintBoundaryEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem registers_cast_apply {I : Inventory} (S : Schedule I)
    {A B : Finset (Fin S.visits)} (h : A=B) (x : Registers S A) (v : {v // v∈B}) :
    (Equiv.cast (congrArg (Registers S) h) x) v=x ⟨v.val,by rw [h]; exact v.property⟩ := by
  subst B
  rfl

theorem prefixLive_first {I : Inventory} {S : Schedule I} (h : 0<S.visits) :
    prefixLive (firstInputBurst S h)=inputVisits (firstInputBurst S h) := by
  rw [prefixLive_eq,first_released_empty,first_inputs]
  simp

def firstPartnerBasis {I : Inventory} {S : Schedule I} (h : 0<S.visits) :
    Registers S (released S (recordTime (firstInputBurst S h)))ᶜ ≃ Recorder.Inputs S where
  toFun u v := u ⟨v,by simp only [first_released_empty]; simp⟩
  invFun u v := u v.val
  left_inv _ := rfl
  right_inv _ := rfl

def firstBoundaryDomain {I : Inventory} {S : Schedule I} (h : 0<S.visits) :
    ((PrefixSpace (firstInputBurst S h) × PrefixSpace (firstInputBurst S h)) × Recorder.Inputs S) ≃
      (PrefixSpace (firstInputBurst S h) × (PrefixSpace (firstInputBurst S h) ×
        Registers S (released S (recordTime (firstInputBurst S h)))ᶜ)) where
  toFun q := (q.1.1,(q.1.2,(firstPartnerBasis h).symm q.2))
  invFun q := ((q.1,q.2.1),firstPartnerBasis h q.2.2)
  left_inv q := by simp
  right_inv q := by simp

theorem firstPrefixEmbedding_zero {I : Inventory} {S : Schedule I} (h : 0<S.visits)
    (q : PrefixSpace (firstInputBurst S h) × PrefixSpace (firstInputBurst S h))
    (c : {c // c∈(visitCarriers S (inputVisits (firstInputBurst S h)))ᶜ}) :
    (firstPrefixEmbedding h q).2 c.val=⟨0,I.dim_pos c.val⟩ := by
  have he := (visitPayloadPartition S (inputVisits (firstInputBurst S h))
    (inputVisits_carriers_injective _)).apply_symm_apply
      (firstPrefixPortCoordinates h q.1,fun d => (⟨0,I.dim_pos d.val⟩ : Fin (I.dim d.val)))
  exact congrArg (fun p => p.2 c) he

/-- The full initial Bell/purification embedding becomes the canonical
boundary embedding after the actual first-burst visit SWAPs. -/
theorem first_boundary_embedding_route {I : Inventory} {S : Schedule I} (h : 0<S.visits)
    (q : ((PrefixSpace (firstInputBurst S h) × PrefixSpace (firstInputBurst S h)) × Recorder.Inputs S)) :
    gauge S (burstMemoryDim S) (inputVisits (firstInputBurst S h))
      (inputVisits_carriers_injective _) (bellProductEmbedding (firstPrefixEmbedding h) q)=
      canonicalRawEmbedding (firstInputBurst S h) (firstBoundaryDomain h q) := by
  let b := firstInputBurst S h
  let V := inputVisits b
  let hc := inputVisits_carriers_injective b
  let old := bellProductEmbedding (firstPrefixEmbedding h) q
  let u := (firstPartnerBasis h).symm q.2
  apply (recordCoordinates S (burstMemoryDim S) (arrived S (recordTime b)) (released S (recordTime b))).injective
  change (recordCoordinates S _ _ _) (gauge S _ V hc old)=
    (recordCoordinates S _ _ _) ((recordCoordinates S _ _ _).symm
      (q.1.1,canonicalEnvironmentEmbedding b (q.1.2,u)))
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · apply Prod.ext
    · funext v
      change (gauge S _ V hc old).1.1 v.val=q.1.1.1 v
      have hv : v.val∈V := by simpa only [V,b,first_inputs] using v.property
      rw [gauge_input_mem S _ V hc v.val hv]
      have he := firstPrefixEmbedding_selected h q.1 ⟨v.val,hv⟩
      have ht := registers_cast_apply S (first_inputs S h) q.1.1.1 ⟨v.val,hv⟩
      exact he.trans ht
    · funext v
      have hf : False := by simpa [b,first_released_empty] using v.property
      exact hf.elim
  · apply Prod.ext
    · apply Prod.ext
      · funext v
        change (gauge S _ V hc old).1.1 v.val=prefixTailInputs b u v
        have hv : v.val∉V := by
          have hh := Finset.mem_compl.mp v.property
          simpa only [V,b,first_inputs] using hh
        rw [gauge_preserves_input S _ V hc v.val hv]
        rfl
      · funext v
        change (gauge S _ V hc old).1.2 v.val=u v
        rw [gauge_preserves_partners]
        rfl
    · apply Prod.ext
      · change (gauge S _ V hc old).2.1=prefixTailPayload b u
        apply (visitPayloadPartition S (prefixLive b)
          (activeVisits_carriers_injective S (prefixCut b) _ (Finset.Subset.refl _))).injective
        rw [prefixTailPayload,Equiv.apply_symm_apply]
        apply Prod.ext
        · funext v
          change (gauge S _ V hc old).2.1 (S.carrier v.val)=u ⟨v.val,prefixLive_unreleased b v.property⟩
          have hv : v.val∈V := by simpa only [V,b,prefixLive_first] using v.property
          rw [gauge_payload_mem S _ V hc v.val hv]
          rfl
        · funext c
          change (gauge S _ V hc old).2.1 c.val=⟨0,I.dim_pos c.val⟩
          have hcV : c.val∈(visitCarriers S V)ᶜ := by
            simpa only [V,b,prefixLive_first] using c.property
          rw [gauge_preserves_carrier S _ V hc c.val (by
            intro v hv he
            exact Finset.mem_compl.mp hcV (Finset.mem_image.mpr ⟨v,hv,he.symm⟩))]
          exact firstPrefixEmbedding_zero h q.1 ⟨c.val,hcV⟩
      · change (gauge S _ V hc old).2.2=canonicalMemoryEmbedding b q.1.2
        rw [gauge_preserves_memory]
        rfl

theorem first_initial_gauge_vector {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0<S.visits)
    (t : Tester S (burstMemoryDim S)) (ht : t.initial=firstPrefixInitialVector Z hZ h)
    (x : Raw S (burstMemoryDim S)) :
    amplitudes t (allBellSource S) 0
      (gauge S _ (inputVisits (firstInputBurst S h)) (inputVisits_carriers_injective _) x)=
      canonicalPrefixVector Z hZ (firstInputBurst S h) x := by
  let b := firstInputBurst S h
  let σ := gauge S (burstMemoryDim S) (inputVisits b) (inputVisits_carriers_injective b)
  let v := prefixPurification S Z hZ b
  have he := embedded_vector_transport (bellProductEmbedding (firstPrefixEmbedding h))
    (canonicalRawEmbedding b) (firstBoundaryDomain h) σ (first_boundary_embedding_route h)
    (fun q => v q.1) (fun q => v (q.1,q.2.1)) (fun _ => rfl) x
  rw [gauge_symm] at he
  rw [bellProductEmbedding_vector,canonicalPrefixVector_embedding] at he
  change allBellSource S (σ x).1*firstPrefixInitialVector Z hZ h ((σ x).2.2,(σ x).2.1)=_ at he
  simpa only [amplitudes,ht] using he

theorem first_boundary_execution {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0<S.visits)
    (t : Tester S (burstMemoryDim S)) (ht : t.initial=firstPrefixInitialVector Z hZ h)
    (hg : ∀ k : Cut S, k.val<recordTime (firstInputBurst S h) → t.gate k=1) :
    amplitudes t (allBellSource S) (recordTime (firstInputBurst S h))=
      canonicalPrefixVector Z hZ (firstInputBurst S h) := by
  let k : Cut S := ⟨0,by omega⟩
  have hi : amplitudes t (allBellSource S) 1=amplitudes t (allBellSource S) 0 := by
    funext x
    simp only [amplitudes,dif_pos (by omega : 0<2*S.visits+1)]
    rw [step_identity_gate t k (hg k (by simp [k,recordTime]))]
    rw [wire_identity_of_no_arrival _ k (by intro v; change (S.position (v,false)).val+1≠0; omega)]
    rfl
  funext x
  have he := input_burst_execution t (allBellSource S) (firstInputBurst S h) (fun k _ hk => hg k hk) x
  change amplitudes t (allBellSource S) (recordTime (firstInputBurst S h)) x=
    amplitudes t (allBellSource S) 1
      (gauge S _ (inputVisits (firstInputBurst S h)) (inputVisits_carriers_injective _) x) at he
  rw [hi] at he
  exact he.trans (first_initial_gauge_vector Z hZ h t ht x)

theorem first_prefix_realized {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0<S.visits)
    (t : Tester S (burstMemoryDim S)) (ht : t.initial=firstPrefixInitialVector Z hZ h)
    (hg : ∀ k : Cut S, k.val<recordTime (firstInputBurst S h) → t.gate k=1) :
    prefixGram (firstInputBurst S h) t=Z (firstInputBurst S h) :=
  prefixGram_of_canonical_vector Z hZ t _ (first_boundary_execution Z hZ h t ht hg)

end ScheduleLaw.Blueprint
