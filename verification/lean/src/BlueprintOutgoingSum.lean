import BlueprintIncomingSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def burstLocalInput {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    BurstInputs b hb :=
  (burstInputPortCoordinates b hb).symm (localInputCoordinates b z.2).1

theorem burstOutgoingMatrix_entry {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ)
    (a : BurstInputs b hb × (PrefixSpace b ⊕ (PrefixSpace (previousInput b hb) × BurstOutputs b hb))) :
    burstOutgoingMatrix b hb z a=
      if z.1=paddedMemoryEmbedding b hb a.2 ∧
        (localInputCoordinates b z.2).1=burstInputPortCoordinates b hb a.1 ∧
        (localInputCoordinates b z.2).2=(fun c => ⟨0,I.dim_pos c.val⟩) then 1 else 0 := by
  change localPortMatrix S _ _ _ _ _ (paddedMemoryEmbedding b hb)
    (fun c => ⟨0,I.dim_pos c.val⟩) z (a.2,burstInputPortCoordinates b hb a.1)=_
  exact localPortMatrix_entry S _ _ _ _ _ _ _ z _

theorem outgoing_record_sum {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S)
    (hb : 0<(inputRank b).val)
    (x : PrefixSpace (previousInput b hb) × BurstOutputs b hb)
    (z : Fin (burstMemoryDim S) × Restricted I (held S (burstPreparationCut b))ᶜ) :
    (∑ a, paddedBurstAmplitude (m := PrefixSpace (previousInput b hb))
      (currentPrefixAmplitude Z hZ b hb) x a * burstOutgoingMatrix b hb z a)=
      if (localInputCoordinates b z.2).2=(fun c => ⟨0,I.dim_pos c.val⟩) then
        canonicalRecordAmplitude Z hZ b
          ((prefixStepCoordinates b hb).symm (x,burstLocalInput b hb z)) z.1 else 0 := by
  classical
  simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,paddedBurstAmplitude,
    zero_mul,Finset.sum_const_zero,add_zero]
  simp_rw [burstOutgoingMatrix_entry]
  have he (i : BurstInputs b hb) : (localInputCoordinates b z.2).1=burstInputPortCoordinates b hb i ↔
      i=burstLocalInput b hb z := by
    change _ ↔ i=(burstInputPortCoordinates b hb).symm (localInputCoordinates b z.2).1
    rw [Equiv.eq_symm_apply]
    exact eq_comm
  simp_rw [he,paddedMemoryEmbedding_canonical]
  by_cases hr : (localInputCoordinates b z.2).2=(fun c => ⟨0,I.dim_pos c.val⟩)
  · rw [Finset.sum_eq_single (burstLocalInput b hb z)]
    · simp [hr,canonicalRecordAmplitude,currentPrefixAmplitude,Fintype.sum_prod_type]
    · intro i hi hn
      simp [hn]
    · simp
  · simp [hr]

end ScheduleLaw.Blueprint
