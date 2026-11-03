import PhaseLocalHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhasePayloadSplit
open History PhaseLocalHamiltonian

theorem held_carrier (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (c : Fin I.count) (hc : c∈A) :
    carrierObservable I b c=
      (((1 : Mat (Fin b)) ⊗ₖ component I A ⟨c,hc⟩) ⊗ₖ (1 : Mat (Restricted I Aᶜ))).submatrix
        (bodyPartition I b A) (bodyPartition I b A) := by
  ext i j
  change (if i.1=j.1 ∧ (∀ d, d≠c → i.2 d=j.2 d) then 1 else 0)*
    (I.H c).matrix (i.2 c) (j.2 c)=
      ((if i.1=j.1 then 1 else 0)*((I.H c).matrix (i.2 c) (j.2 c)*
        (if ∀ d : {d // d∈A},d.val≠c → i.2 d.val=j.2 d.val then 1 else 0)))*
          (if restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 then 1 else 0)
  simp only [other_coordinates_owned I A c hc i.2 j.2]
  by_cases hb : i.1=j.1 <;>
    by_cases hh : ∀ d : {d // d∈A},d.val≠c → i.2 d.val=j.2 d.val <;>
    by_cases hr : restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 <;> simp [hb,hh,hr]

theorem unheld_carrier (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (c : Fin I.count) (hc : c∉A) :
    carrierObservable I b c=
      ((1 : Mat (Fin b × Restricted I A)) ⊗ₖ component I Aᶜ ⟨c,Finset.mem_compl.mpr hc⟩).submatrix
        (bodyPartition I b A) (bodyPartition I b A) := by
  ext i j
  change (if i.1=j.1 ∧ (∀ d, d≠c → i.2 d=j.2 d) then 1 else 0)*
    (I.H c).matrix (i.2 c) (j.2 c)=
      (if (i.1,restrictPayload I A i.2)=(j.1,restrictPayload I A j.2) then 1 else 0)*
        ((I.H c).matrix (i.2 c) (j.2 c)*
          (if ∀ d : {d // d∈Aᶜ},d.val≠c → i.2 d.val=j.2 d.val then 1 else 0))
  simp only [Prod.mk.injEq,other_coordinates_partition I A c hc i.2 j.2]
  by_cases hb : i.1=j.1 <;>
    by_cases hh : restrictPayload I A i.2=restrictPayload I A j.2 <;>
    by_cases hr : ∀ d : {d // d∈Aᶜ},d.val≠c → i.2 d.val=j.2 d.val <;> simp [hb,hh,hr]

def carrierPartition (I : Inventory) (A : Finset (Fin I.count)) :
    {c // c∈A} ⊕ {c // c∈Aᶜ} ≃ Fin I.count where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun c := if h : c∈A then Sum.inl ⟨c,h⟩ else Sum.inr ⟨c,Finset.mem_compl.mpr h⟩
  left_inv x := by
    cases x with
    | inl c => simp [c.property]
    | inr c => simp [Finset.mem_compl.mp c.property]
  right_inv c := by
    by_cases h : c∈A <;> simp [h]

theorem payload_carriers (I : Inventory) (b : ℕ) :
    (1 : Mat (Fin b)) ⊗ₖ payloadHamiltonian I=∑ c,carrierObservable I b c := by
  ext i j
  simp only [kroneckerMap_apply,Matrix.one_apply,payloadHamiltonian,Matrix.sum_apply,carrierObservable]
  by_cases hb : i.1=j.1
  · simp only [hb,if_true,true_and,one_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · simp only [hb,if_false,false_and,zero_mul,Finset.sum_const_zero]

end ScheduleLaw.Blueprint.PhasePayloadSplit
