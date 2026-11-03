import BlueprintBurstRouting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

abbrev BurstWaste {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  Σ h : {u : Unit // 0 < (inputRank b).val},
    (PrefixSpace (previousInput b h.property) × BurstOutputs b h.property)

abbrev BurstMemoryCell {I : Inventory} {S : Schedule I} (b : InputBurst S) :=
  PrefixSpace b ⊕ BurstWaste b

abbrev BurstMemoryPool {I : Inventory} (S : Schedule I) :=
  Σ b : InputBurst S, BurstMemoryCell b

def burstMemoryDim {I : Inventory} (S : Schedule I) : ℕ := Fintype.card (BurstMemoryPool S)+1

theorem burstMemoryDim_pos {I : Inventory} (S : Schedule I) : 0 < burstMemoryDim S :=
  Nat.succ_pos _

def memoryCellEmbedding {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    BurstMemoryCell b ↪ Fin (burstMemoryDim S) :=
  ((Function.Embedding.sigmaMk b).trans (Fintype.equivFin (BurstMemoryPool S)).toEmbedding).trans
    (Fin.castLEEmb (Nat.le_succ _))

def canonicalMemoryEmbedding {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    PrefixSpace b ↪ Fin (burstMemoryDim S) :=
  Function.Embedding.inl.trans (memoryCellEmbedding b)

def paddedMemoryEmbedding {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    (PrefixSpace b ⊕ (PrefixSpace (previousInput b hb) × BurstOutputs b hb)) ↪ Fin (burstMemoryDim S) :=
  (Function.Embedding.sumMap (Function.Embedding.refl _)
    (Function.Embedding.sigmaMk (⟨(),hb⟩ : {u : Unit // 0 < (inputRank b).val}))).trans
      (memoryCellEmbedding b)

theorem paddedMemoryEmbedding_canonical {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) (x : PrefixSpace b) :
    paddedMemoryEmbedding b hb (Sum.inl x)=canonicalMemoryEmbedding b x := rfl

theorem localVisitPartition_selected {I : Inventory} (S : Schedule I)
    (A : Finset (Fin I.count)) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hVA : visitCarriers S V ⊆ A)
    (p : Restricted I A) (v : {v // v ∈ V}) :
    (localVisitPartition S A V hc hVA p).1 v =
      p ⟨S.carrier v.val,hVA (Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩)⟩ := rfl

def localPortEmbedding {I : Inventory} (S : Schedule I) (r : ℕ)
    (A : Finset (Fin I.count)) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hVA : visitCarriers S V ⊆ A)
    {m : Type} (e : m ↪ Fin r) (rest : Restricted I (A \ visitCarriers S V)) :
    (m × Registers S V) ↪ (Fin r × Restricted I A) where
  toFun x := (e x.1,(localVisitPartition S A V hc hVA).symm (x.2,rest))
  inj' := by
    intro x y h
    have hm : x.1=y.1 := e.injective (congrArg Prod.fst h)
    have hp := congrArg (localVisitPartition S A V hc hVA) (congrArg Prod.snd h)
    have hport : x.2=y.2 := by
      simpa only [Equiv.apply_symm_apply] using congrArg Prod.fst hp
    exact Prod.ext hm hport

theorem localPortEmbedding_selected {I : Inventory} (S : Schedule I) (r : ℕ)
    (A : Finset (Fin I.count)) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hVA : visitCarriers S V ⊆ A)
    {m : Type} (e : m ↪ Fin r) (rest : Restricted I (A \ visitCarriers S V))
    (x : m × Registers S V) (v : {v // v ∈ V}) :
    (localPortEmbedding S r A V hc hVA e rest x).2
      ⟨S.carrier v.val,hVA (Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩)⟩ = x.2 v := by
  have h := congrArg (fun p => p.1 v)
    ((localVisitPartition S A V hc hVA).apply_symm_apply (x.2,rest))
  simpa only [localVisitPartition_selected,localPortEmbedding] using h

def localPortMatrix {I : Inventory} (S : Schedule I) (r : ℕ)
    (A : Finset (Fin I.count)) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hVA : visitCarriers S V ⊆ A)
    {m : Type} (e : m ↪ Fin r) (rest : Restricted I (A \ visitCarriers S V)) :
    Matrix (Fin r × Restricted I A) (m × Registers S V) ℂ :=
  registerEmbedding (localPortEmbedding S r A V hc hVA e rest)

theorem localPortMatrix_isometry {I : Inventory} (S : Schedule I) (r : ℕ)
    (A : Finset (Fin I.count)) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hVA : visitCarriers S V ⊆ A)
    {m : Type} [Fintype m] [DecidableEq m]
    (e : m ↪ Fin r) (rest : Restricted I (A \ visitCarriers S V)) :
    (localPortMatrix S r A V hc hVA e rest)ᴴ * localPortMatrix S r A V hc hVA e rest=1 :=
  registerEmbedding_isometry _

def burstInputPortCoordinates {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    BurstInputs b hb ≃ Registers S (inputVisits b) :=
  Equiv.cast (congrArg (Registers S) (new_inputs_exact b hb))

def burstIncomingMatrix {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    Matrix (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ)
      (PrefixSpace (previousInput b hb) × BurstOutputs b hb) ℂ :=
  localPortMatrix S _ _ (newOutputs b hb)
    (activeVisits_carriers_injective S _ _ (new_outputs_active b hb)) (output_carriers_available b hb)
    (canonicalMemoryEmbedding (previousInput b hb)) (fun c => ⟨0,I.dim_pos c.val⟩)

def burstOutgoingEmbedding {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    (BurstInputs b hb × (PrefixSpace b ⊕
      (PrefixSpace (previousInput b hb) × BurstOutputs b hb))) ↪
        (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :=
  ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (burstInputPortCoordinates b hb))).toEmbedding.trans
      (localPortEmbedding S _ _ (inputVisits b) (inputVisits_carriers_injective b)
        (input_carriers_available b) (paddedMemoryEmbedding b hb) (fun c => ⟨0,I.dim_pos c.val⟩))

def burstOutgoingMatrix {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    Matrix (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ)
      (BurstInputs b hb × (PrefixSpace b ⊕
        (PrefixSpace (previousInput b hb) × BurstOutputs b hb))) ℂ :=
  registerEmbedding (burstOutgoingEmbedding b hb)

theorem burstIncomingMatrix_isometry {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    (burstIncomingMatrix b hb)ᴴ * burstIncomingMatrix b hb=1 :=
  localPortMatrix_isometry S _ _ _ _ _ _ _

theorem burstOutgoingMatrix_isometry {I : Inventory} {S : Schedule I}
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    (burstOutgoingMatrix b hb)ᴴ * burstOutgoingMatrix b hb=1 := registerEmbedding_isometry _

/-- One fixed schedule-dependent memory suffices for every completed burst
gate. Its ports are the actual unheld carriers and earlier prefix Grams are retained. -/
theorem lawful_burst_gate {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z)
    (b : InputBurst S) (hb : 0 < (inputRank b).val) :
    ∃ U : Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ),
      IsUnitary U ∧
      (∀ x o w, (∑ m, previousPrefixAmplitude Z hZ b hb x m *
          (U*burstIncomingMatrix b hb) w (m,o)) =
        ∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (x,o) a * burstOutgoingMatrix b hb w a) ∧
      ∀ t : Tester S (burstMemoryDim S),
        ∃ u : Tester S (burstMemoryDim S), u.initial=t.initial ∧
          (∀ a : InputBurst S, a < b → prefixGram a u=prefixGram a t) ∧
          u.gate (burstPreparationCut b)=localRegisterGate I _ _ U * t.gate (burstPreparationCut b) := by
  obtain ⟨U,hU,hamp⟩ := canonical_prefix_square_completion Z hZ b hb
    (burstIncomingMatrix b hb) (burstOutgoingMatrix b hb)
    (burstIncomingMatrix_isometry b hb) (burstOutgoingMatrix_isometry b hb)
  refine ⟨U,hU,hamp,?_⟩
  intro t
  refine ⟨postcomposeTester t (burstPreparationCut b) U hU,rfl,?_,?_⟩
  · intro a hab
    exact postcomposeTester_earlier_prefix t b U hU a hab
  · simp [postcomposeTester]

end ScheduleLaw.Blueprint
