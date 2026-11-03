import BlueprintBurstEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem burstPreparationCut_injective {I : Inventory} {S : Schedule I} :
    Function.Injective (burstPreparationCut (S := S)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Fin.ext
  exact congrArg (fun k : Cut S => k.val) h

theorem identity_local (I : Inventory) (r : ℕ) (A : Finset (Fin I.count)) :
    LocalOn I r A (1 : Mat (Fin r × Payload I)) := by
  have he : localRegisterGate I r A (1 : Mat (Fin r × Restricted I A))=1 := by
    unfold localRegisterGate
    rw [one_kronecker_one,submatrix_one_equiv]
  rw [← he]
  exact localRegisterGate_local I r A 1 ⟨by simp,by simp⟩

theorem positive_burst_gate_congr {I : Inventory} {S : Schedule I}
    (U : (b : InputBurst S) → (hb : 0 < (inputRank b).val) →
      Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ))
    {a b : InputBurst S} (ha : 0 < (inputRank a).val) (hb : 0 < (inputRank b).val)
    (h : a=b) :
    localRegisterGate I _ (held S (burstPreparationCut a))ᶜ (U a ha) =
      localRegisterGate I _ (held S (burstPreparationCut b))ᶜ (U b hb) := by
  subst b
  rfl

/-- Assemble all canonical higher-burst contacts into one actual lawful
Tester with one fixed memory. Initial purification and prefix-state induction
remain separate from this gate construction. -/
theorem canonical_burst_tester_gates {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z)
    (ψ : Fin (burstMemoryDim S) × Payload I → ℂ)
    (hψ : ∑ x,Complex.normSq (ψ x)=1) :
    ∃ (t : Tester S (burstMemoryDim S))
      (U : (b : InputBurst S) → (hb : 0 < (inputRank b).val) →
        Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ)),
      t.initial=ψ ∧
      (∀ b hb, IsUnitary (U b hb)) ∧
      (∀ b hb, t.gate (burstPreparationCut b)=localRegisterGate I _ _ (U b hb)) ∧
      (∀ k : Cut S, (∀ b : InputBurst S, 0 < (inputRank b).val → burstPreparationCut b ≠ k) → t.gate k=1) ∧
      ∀ b hb x o w, (∑ m, previousPrefixAmplitude Z hZ b hb x m *
          (U b hb*burstIncomingMatrix b hb) w (m,o)) =
        ∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (x,o) a * burstOutgoingMatrix b hb w a := by
  classical
  have hchoose : ∀ (b : InputBurst S) (hb : 0 < (inputRank b).val),
      ∃ U : Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ),
      IsUnitary U ∧ ∀ x o w, (∑ m, previousPrefixAmplitude Z hZ b hb x m *
          (U*burstIncomingMatrix b hb) w (m,o)) =
        ∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (x,o) a * burstOutgoingMatrix b hb w a := by
    intro b hb
    obtain ⟨U,hU,ha,_⟩ := lawful_burst_gate Z hZ b hb
    exact ⟨U,hU,ha⟩
  choose U hU hamp using hchoose
  let Q (k : Cut S) : Prop := ∃ b : InputBurst S, 0 < (inputRank b).val ∧ burstPreparationCut b=k
  let stage (k : Cut S) (h : Q k) : InputBurst S := Classical.choose h
  have hstage (k : Cut S) (h : Q k) : 0 < (inputRank (stage k h)).val :=
    (Classical.choose_spec h).1
  have hcut (k : Cut S) (h : Q k) : burstPreparationCut (stage k h)=k :=
    (Classical.choose_spec h).2
  let gate (k : Cut S) : Mat (Fin (burstMemoryDim S) × Payload I) :=
    if h : Q k then localRegisterGate I _ (held S (burstPreparationCut (stage k h)))ᶜ
      (U (stage k h) (hstage k h)) else 1
  have hgateU (k : Cut S) : IsUnitary (gate k) := by
    dsimp only [gate]
    split_ifs with h
    · exact localRegisterGate_unitary I _ _ _ (hU _ _)
    · constructor <;> simp
  have hgateL (k : Cut S) : LocalOn I (burstMemoryDim S) (held S k)ᶜ (gate k) := by
    dsimp only [gate]
    split_ifs with h
    · have he := congrArg (fun l : Cut S => LocalOn I (burstMemoryDim S) (held S l)ᶜ
          (localRegisterGate I _ (held S (burstPreparationCut (stage k h)))ᶜ
            (U (stage k h) (hstage k h)))) (hcut k h)
      exact he.mp (localRegisterGate_local I _ _ _ (hU _ _))
    · exact identity_local I _ _
  let t : Tester S (burstMemoryDim S) := {
    initial := ψ
    normalized := hψ
    gate := gate
    unitary := hgateU
    gate_local := hgateL }
  refine ⟨t,U,rfl,hU,?_,?_,hamp⟩
  · intro b hb
    have hq : Q (burstPreparationCut b) := ⟨b,hb,rfl⟩
    have hs : stage (burstPreparationCut b) hq=b :=
      burstPreparationCut_injective (hcut (burstPreparationCut b) hq)
    change gate (burstPreparationCut b)=_
    simp only [gate,dif_pos hq]
    exact positive_burst_gate_congr U (hstage _ hq) hb hs
  · intro k hn
    have hq : ¬Q k := by
      rintro ⟨b,hb,h⟩
      exact hn b hb h
    change gate k=1
    simp only [gate,dif_neg hq]

end ScheduleLaw.Blueprint
