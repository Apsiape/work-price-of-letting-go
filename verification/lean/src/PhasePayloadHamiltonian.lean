import PhasePayloadSplit

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhasePayloadHamiltonian
open History PhaseLocalHamiltonian PhasePayloadSplit

theorem carrier_sum (I : Inventory) (b : ℕ) (A : Finset (Fin I.count)) :
    (∑ c,carrierObservable I b c)=
      (∑ c : {c // c∈A},carrierObservable I b c.val)+
      (∑ c : {c // c∈Aᶜ},carrierObservable I b c.val) := by
  have h := Equiv.sum_comp (carrierPartition I A) (carrierObservable I b)
  simpa only [Fintype.sum_sum_type,carrierPartition,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr] using h.symm

theorem body_part (I : Inventory) (b : ℕ) (A : Finset (Fin I.count)) (H : Mat (Fin b)) :
    H ⊗ₖ (1 : Mat (Payload I))=
      ((H ⊗ₖ (1 : Mat (Restricted I A))) ⊗ₖ (1 : Mat (Restricted I Aᶜ))).submatrix
        (bodyPartition I b A) (bodyPartition I b A) := by
  ext i j
  change H i.1 j.1*(if i.2=j.2 then 1 else 0)=
    (H i.1 j.1*(if restrictPayload I A i.2=restrictPayload I A j.2 then 1 else 0))*
      (if restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 then 1 else 0)
  have hp : i.2=j.2 ↔ restrictPayload I A i.2=restrictPayload I A j.2 ∧
      restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 := by
    constructor
    · intro h; exact ⟨congrArg (restrictPayload I A) h,congrArg (restrictPayload I Aᶜ) h⟩
    · rintro ⟨h1,h2⟩
      exact (payloadPartition I A).injective (Prod.ext h1 h2)
  simp only [hp]
  by_cases hh : restrictPayload I A i.2=restrictPayload I A j.2 <;>
    by_cases hr : restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 <;> simp [hh,hr]

private theorem sum_submatrix {a b k : Type} [Fintype k] (E : a → b) (M : k → Mat b) :
    (∑ i,M i).submatrix E E=∑ i,(M i).submatrix E E := by
  ext i j
  simp only [submatrix_apply,Matrix.sum_apply]

private theorem sum_kron_left {a b k : Type} [Fintype k] (M : k → Mat a) (N : Mat b) :
    (∑ i,M i) ⊗ₖ N=∑ i,M i ⊗ₖ N := by
  ext i j
  simp only [kroneckerMap_apply,Matrix.sum_apply,Finset.sum_mul]

private theorem sum_kron_right {a b k : Type} [Fintype k] (M : Mat a) (N : k → Mat b) :
    M ⊗ₖ (∑ i,N i)=∑ i,M ⊗ₖ N i := by
  ext i j
  simp only [kroneckerMap_apply,Matrix.sum_apply,Finset.mul_sum]

private theorem reindex_add {a b : Type} (E : a → b) (M N : Mat b) :
    (M+N).submatrix E E=M.submatrix E E+N.submatrix E E := rfl

theorem total (I : Inventory) (b : ℕ) (A : Finset (Fin I.count)) (H : Mat (Fin b)) :
    H ⊗ₖ (1 : Mat (Payload I))+(1 : Mat (Fin b)) ⊗ₖ payloadHamiltonian I=
      (((H ⊗ₖ (1 : Mat (Restricted I A))+(1 : Mat (Fin b)) ⊗ₖ (restricted I A).matrix) ⊗ₖ
        (1 : Mat (Restricted I Aᶜ)))+
        (1 : Mat (Fin b × Restricted I A)) ⊗ₖ (restricted I Aᶜ).matrix).submatrix
          (bodyPartition I b A) (bodyPartition I b A) := by
  rw [payload_carriers,carrier_sum,body_part I b A H]
  have hh : (∑ c : {c // c∈A},carrierObservable I b c.val)=
      ∑ c : {c // c∈A},(((1 : Mat (Fin b)) ⊗ₖ component I A c) ⊗ₖ
        (1 : Mat (Restricted I Aᶜ))).submatrix (bodyPartition I b A) (bodyPartition I b A) :=
    Finset.sum_congr rfl (fun c _ => held_carrier I b A c.val c.property)
  have hr : (∑ c : {c // c∈Aᶜ},carrierObservable I b c.val)=
      ∑ c : {c // c∈Aᶜ},((1 : Mat (Fin b × Restricted I A)) ⊗ₖ component I Aᶜ c).submatrix
        (bodyPartition I b A) (bodyPartition I b A) :=
    Finset.sum_congr rfl (fun c _ => unheld_carrier I b A c.val (Finset.mem_compl.mp c.property))
  rw [hh,hr]
  rw [← sum_submatrix,← sum_submatrix,← reindex_add,← reindex_add]
  congr 1
  rw [← sum_kron_left,← sum_kron_right,← sum_kron_right]
  simp only [restricted,add_kronecker,add_assoc]


end ScheduleLaw.Blueprint.PhasePayloadHamiltonian
