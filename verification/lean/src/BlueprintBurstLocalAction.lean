import BlueprintOutgoingSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem raw_local_gate_entry {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (U : Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ))
    (x y : Raw S (burstMemoryDim S)) :
    (if x.1=y.1 then (1:ℂ) else 0)*localRegisterGate I _ _ U (x.2.2,x.2.1) (y.2.2,y.2.1)=
      (if (rawBurstCoordinates b x).1=(rawBurstCoordinates b y).1 then 1 else 0)*
        U (rawBurstCoordinates b x).2 (rawBurstCoordinates b y).2 := by
  classical
  have hcc : restrictPayload I (held S (burstPreparationCut b))ᶜᶜ x.2.1=
      restrictPayload I (held S (burstPreparationCut b))ᶜᶜ y.2.1 ↔
      restrictPayload I (held S (burstPreparationCut b)) x.2.1=
        restrictPayload I (held S (burstPreparationCut b)) y.2.1 := by
    constructor
    · intro he
      funext d
      exact congrFun he ⟨d.val,Finset.mem_compl.mpr (fun hn => Finset.mem_compl.mp hn d.property)⟩
    · intro he
      funext d
      exact congrFun he ⟨d.val,by simpa only [Finset.mem_compl,not_not] using d.property⟩
  change (if x.1=y.1 then (1:ℂ) else 0)*
    (U (x.2.2,restrictPayload I (held S (burstPreparationCut b))ᶜ x.2.1)
      (y.2.2,restrictPayload I (held S (burstPreparationCut b))ᶜ y.2.1)*
      (if restrictPayload I (held S (burstPreparationCut b))ᶜᶜ x.2.1=
        restrictPayload I (held S (burstPreparationCut b))ᶜᶜ y.2.1 then 1 else 0))=_
  simp only [hcc]
  by_cases hs : x.1=y.1 <;>
    by_cases hh : restrictPayload I (held S (burstPreparationCut b)) x.2.1=
      restrictPayload I (held S (burstPreparationCut b)) y.2.1 <;>
    simp [hs,hh,rawBurstCoordinates,Prod.ext_iff]

theorem step_local_section {I : Inventory} {S : Schedule I}
    (t : Tester S (burstMemoryDim S)) (b : InputBurst S)
    (U : Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ))
    (hg : t.gate (burstPreparationCut b)=localRegisterGate I _ _ U)
    (hw : wire (burstPreparationCut b) (burstMemoryDim S)=1)
    (v : Raw S (burstMemoryDim S) → ℂ)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    step t (burstPreparationCut b) v ((rawBurstCoordinates b).symm (c,z))=
      ∑ w, U z w*v ((rawBurstCoordinates b).symm (c,w)) := by
  classical
  letI : NeZero (burstMemoryDim S) := ⟨(burstMemoryDim_pos S).ne'⟩
  letI : Nonempty (Payload I) := ⟨fun d => ⟨0,I.dim_pos d⟩⟩
  letI : Nonempty (Restricted I (held S (burstPreparationCut b))) := ⟨fun d => ⟨0,I.dim_pos d.val⟩⟩
  letI : Nonempty (Restricted I (held S (burstPreparationCut b))ᶜ) := ⟨fun d => ⟨0,I.dim_pos d.val⟩⟩
  let x := (rawBurstCoordinates b).symm (c,z)
  have hfull : step t (burstPreparationCut b) v x=
      ∑ y : Raw S (burstMemoryDim S),
        ((if x.1=y.1 then (1:ℂ) else 0)*localRegisterGate I _ _ U
          (x.2.2,x.2.1) (y.2.2,y.2.1))*v y := by
    simp [step,hg,hw,Fintype.sum_prod_type,ite_mul]
  rw [hfull]
  simp_rw [raw_local_gate_entry b U]
  rw [←(rawBurstCoordinates b).symm.sum_comp
    (fun y => ((if (rawBurstCoordinates b x).1=(rawBurstCoordinates b y).1 then (1:ℂ) else 0)*
      U (rawBurstCoordinates b x).2 (rawBurstCoordinates b y).2)*v y)]
  simp [x,Fintype.sum_prod_type,ite_mul]

theorem burst_section_transport {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (U : Mat (Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ))
    (hamp : ∀ x o w, (∑ m, previousPrefixAmplitude Z hZ b hb x m *
      (U*burstIncomingMatrix b hb) w (m,o))=
        ∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
          (currentPrefixAmplitude Z hZ b hb) (x,o) a * burstOutgoingMatrix b hb w a)
    (c : Recorder.Stock S × Restricted I (held S (burstPreparationCut b)))
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (∑ w, U z w*canonicalPrefixVector Z hZ (previousInput b hb)
      ((rawBurstCoordinates b).symm (c,w)))=
      canonicalPrefixVector Z hZ b
        (gauge S _ (inputVisits b) (inputVisits_carriers_injective b)
          ((rawBurstCoordinates b).symm (c,z))) := by
  classical
  simp_rw [canonical_incoming_section Z hZ b hb]
  rw [canonical_outgoing_section Z hZ b hb,←hamp]
  simp only [Matrix.mul_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro w hw
  ring

end ScheduleLaw.Blueprint
