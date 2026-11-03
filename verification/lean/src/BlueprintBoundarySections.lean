import BlueprintGapGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def rawBurstCoordinates {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    Raw S (burstMemoryDim S) ≃
      (Recorder.Stock S × Restricted I (held S (burstPreparationCut b))) ×
        (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) where
  toFun x := ((x.1,restrictPayload I (held S (burstPreparationCut b)) x.2.1),
    (x.2.2,restrictPayload I (held S (burstPreparationCut b))ᶜ x.2.1))
  invFun x := (x.1.1,((payloadPartition I (held S (burstPreparationCut b))).symm (x.1.2,x.2.2),x.2.1))
  left_inv x := by
    change (x.1,((payloadPartition I (held S (burstPreparationCut b))).symm
      ((payloadPartition I (held S (burstPreparationCut b))) x.2.1),x.2.2))=x
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    have h := (payloadPartition I (held S (burstPreparationCut b))).apply_symm_apply (x.1.2,x.2.2)
    have hh := congrArg Prod.fst h
    have hf := congrArg Prod.snd h
    change restrictPayload I (held S (burstPreparationCut b))
      ((payloadPartition I (held S (burstPreparationCut b))).symm (x.1.2,x.2.2))=x.1.2 at hh
    change restrictPayload I (held S (burstPreparationCut b))ᶜ
      ((payloadPartition I (held S (burstPreparationCut b))).symm (x.1.2,x.2.2))=x.2.2 at hf
    change ((x.1.1,restrictPayload I (held S (burstPreparationCut b))
      ((payloadPartition I (held S (burstPreparationCut b))).symm (x.1.2,x.2.2))),
      (x.2.1,restrictPayload I (held S (burstPreparationCut b))ᶜ
        ((payloadPartition I (held S (burstPreparationCut b))).symm (x.1.2,x.2.2))))=x
    rw [hh,hf]

theorem rawBurstCoordinates_held {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (x : (Recorder.Stock S × Restricted I (held S (burstPreparationCut b))) ×
      (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ)) :
    restrictPayload I (held S (burstPreparationCut b)) ((rawBurstCoordinates b).symm x).2.1=x.1.2 :=
  congrArg Prod.fst ((payloadPartition I (held S (burstPreparationCut b))).apply_symm_apply (x.1.2,x.2.2))

theorem rawBurstCoordinates_free {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (x : (Recorder.Stock S × Restricted I (held S (burstPreparationCut b))) ×
      (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ)) :
    restrictPayload I (held S (burstPreparationCut b))ᶜ ((rawBurstCoordinates b).symm x).2.1=x.2.2 :=
  congrArg Prod.snd ((payloadPartition I (held S (burstPreparationCut b))).apply_symm_apply (x.1.2,x.2.2))

theorem localPortMatrix_entry {I : Inventory} (S : Schedule I) (r : ℕ)
    (A : Finset (Fin I.count)) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hVA : visitCarriers S V ⊆ A)
    {m : Type} (e : m ↪ Fin r) (rest : Restricted I (A \ visitCarriers S V))
    (z : Fin r × Restricted I A) (q : m × Registers S V) :
    localPortMatrix S r A V hc hVA e rest z q=
      if z.1=e q.1 ∧ (localVisitPartition S A V hc hVA z.2).1=q.2 ∧
        (localVisitPartition S A V hc hVA z.2).2=rest then 1 else 0 := by
  classical
  have he : z=localPortEmbedding S r A V hc hVA e rest q ↔
      z.1=e q.1 ∧ (localVisitPartition S A V hc hVA z.2).1=q.2 ∧
        (localVisitPartition S A V hc hVA z.2).2=rest := by
    change z=(e q.1,(localVisitPartition S A V hc hVA).symm (q.2,rest)) ↔ _
    rw [Prod.ext_iff,Equiv.eq_symm_apply,Prod.mk.injEq]
  simp only [localPortMatrix,registerEmbedding,he]

theorem previousTail_free_port {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (u : Recorder.Inputs S) :
    restrictPayload I (held S (burstPreparationCut b))ᶜ
      (prefixTailPayload (previousInput b hb) (fun v => u v.val))=
      (localOutputCoordinates b hb).symm
        ((fun v => u v.val),fun c => ⟨0,I.dim_pos c.val⟩) := by
  apply (localOutputCoordinates b hb).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext v
    change prefixTailPayload (previousInput b hb) (fun v => u v.val) (S.carrier v.val)=u v.val
    exact prefixTailPayload_live _ _ ⟨v.val,new_outputs_active b hb v.property⟩
  · funext c
    change prefixTailPayload (previousInput b hb) (fun v => u v.val) c.val=⟨0,I.dim_pos c.val⟩
    have hn : c.val∈(visitCarriers S (prefixLive (previousInput b hb)))ᶜ := by
      rw [previous_live_carriers b hb]
      exact Finset.mem_compl.mpr (by
        intro hc
        rcases Finset.mem_union.mp hc with hh|ho
        · exact Finset.mem_compl.mp (Finset.mem_sdiff.mp c.property).1 hh
        · exact (Finset.mem_sdiff.mp c.property).2 ho)
    exact prefixTailPayload_zero _ _ ⟨c.val,hn⟩

theorem currentTail_free_port {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (u : Recorder.Inputs S) :
    restrictPayload I (held S (burstPreparationCut b))ᶜ (prefixTailPayload b (fun v => u v.val))=
      (localInputCoordinates b).symm ((fun v => u v.val),fun c => ⟨0,I.dim_pos c.val⟩) := by
  apply (localInputCoordinates b).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext v
    change prefixTailPayload b (fun v => u v.val) (S.carrier v.val)=u v.val
    exact prefixTailPayload_live _ _ ⟨v.val,inputVisits_active_at_prefix b v.property⟩
  · funext c
    change prefixTailPayload b (fun v => u v.val) c.val=⟨0,I.dim_pos c.val⟩
    have hn : c.val∈(visitCarriers S (prefixLive b))ᶜ := by
      rw [current_live_carriers b hb]
      exact Finset.mem_compl.mpr (by
        intro hc
        rcases Finset.mem_union.mp hc with hh|ho
        · exact Finset.mem_compl.mp (Finset.mem_sdiff.mp c.property).1 hh
        · exact (Finset.mem_sdiff.mp c.property).2 ho)
    exact prefixTailPayload_zero _ _ ⟨c.val,hn⟩

def burstPastRecord {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (s : Recorder.Stock S) : PrefixSpace (previousInput b hb) :=
  (stockPartition S (arrived S (recordTime (previousInput b hb)))
    (released S (recordTime (previousInput b hb))) s).1

def burstOutputRecord {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val) (s : Recorder.Stock S) : BurstOutputs b hb := fun v => s.2 v.val

def burstCommonFactor {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b))) : ℂ := by
  classical
  exact if (∀ v : {v // v∈(arrived S (recordTime (previousInput b hb)))ᶜ}, c.1.1 v.val=c.1.2 v.val) ∧
      c.2=restrictPayload I (held S (burstPreparationCut b))
        (prefixTailPayload (previousInput b hb) (fun v => c.1.2 v.val)) then 1 else 0

theorem incoming_record_sum {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0<(inputRank b).val) (x : PrefixSpace (previousInput b hb)) (o : BurstOutputs b hb)
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (∑ m, previousPrefixAmplitude Z hZ b hb x m*burstIncomingMatrix b hb z (m,o))=
      if (localOutputCoordinates b hb z.2).1=o ∧
        (localOutputCoordinates b hb z.2).2=(fun c => ⟨0,I.dim_pos c.val⟩) then
        canonicalRecordAmplitude Z hZ (previousInput b hb) x z.1 else 0 := by
  classical
  unfold burstIncomingMatrix
  simp_rw [localPortMatrix_entry]
  change (∑ m, previousPrefixAmplitude Z hZ b hb x m *
    if z.1=canonicalMemoryEmbedding (previousInput b hb) m ∧
      (localOutputCoordinates b hb z.2).1=o ∧
      (localOutputCoordinates b hb z.2).2=(fun c => ⟨0,I.dim_pos c.val⟩) then 1 else 0)=_
  by_cases hp : (localOutputCoordinates b hb z.2).1=o <;>
    by_cases hr : (localOutputCoordinates b hb z.2).2=(fun c => ⟨0,I.dim_pos c.val⟩) <;>
    simp [hp,hr,canonicalRecordAmplitude,previousPrefixAmplitude,and_assoc]

end ScheduleLaw.Blueprint
