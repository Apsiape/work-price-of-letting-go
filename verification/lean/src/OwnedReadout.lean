import EmptyContact

/-! Exact local operational readouts from the actual owned state at a cut.
The further factorization of these states through the independent wire Gram
is a separate routing obligation, not an assumption of this module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

def partialRightLinear (a z : Type) [Fintype z] : Mat (a × z) →ₗ[ℂ] Mat a where
  toFun := partialRight
  map_add' A B := by ext i j; exact Finset.sum_add_distrib
  map_smul' c A := by
    ext i j
    change (∑ k, c * A (i,k) (j,k)) = c * ∑ k, A (i,k) (j,k)
    exact (Finset.mul_sum _ _ _).symm

def sandwichLinear {a z : Type} [Fintype a] (K : Matrix z a ℂ) : Mat a →ₗ[ℂ] Mat z where
  toFun A := K * A * Kᴴ
  map_add' A B := by rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' c A := by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

def localContactGate {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S) :
    Mat (Fin e.b × Restricted I (held S k)) := Classical.choose (e.gate_local k)

theorem localContactGate_spec {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S) :
    IsUnitary (localContactGate e k) ∧ ∀ i j,
      e.gate k i j = localContactGate e k (i.1,restrictPayload I (held S k) i.2)
        (j.1,restrictPayload I (held S k) j.2) *
        if restrictPayload I (held S k)ᶜ i.2 = restrictPayload I (held S k)ᶜ j.2 then 1 else 0 :=
  Classical.choose_spec (e.gate_local k)

def ownedMarginal {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (ρ : Mat (Global e r)) : Mat (Fin e.b × Restricted I A) :=
  partialRight (ρ.submatrix (ownershipCoordinates e r A).symm (ownershipCoordinates e r A).symm)

def ownershipEnvironment (I : Inventory) (r : ℕ) (A : Finset (Fin I.count)) :
    Payload I × Fin r ≃ Restricted I A × (Fin r × Restricted I Aᶜ) :=
  ((Equiv.prodCongr (payloadPartition I A) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))

theorem owned_body_marginal {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (ρ : Mat (Global e r)) :
    partialRight (ownedMarginal e r A ρ) = partialRight ρ := by
  ext i j
  change (∑ a : Restricted I A, ∑ z : Fin r × Restricted I Aᶜ,
    ρ (i,((payloadPartition I A).symm (a,z.2),z.1))
      (j,((payloadPartition I A).symm (a,z.2),z.1))) = _
  let f := fun z : Restricted I A × (Fin r × Restricted I Aᶜ) =>
    ρ (i,(ownershipEnvironment I r A).symm z) (j,(ownershipEnvironment I r A).symm z)
  change (∑ a, ∑ z, f (a,z)) = ∑ z, ρ (i,z) (j,z)
  exact (Fintype.sum_prod_type f).symm.trans
    (Equiv.sum_comp (ownershipEnvironment I r A).symm (fun z => ρ (i,z) (j,z)))

theorem owned_tester_invariant {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (ρ : Mat (Global e r)) :
    ownedMarginal e r (held S k) (evolve (liftTesterObservable e r (t.gate k)) ρ) =
      ownedMarginal e r (held S k) ρ := by
  obtain ⟨W,hW,hTW⟩ := t.gate_local k
  have he : ∀ i j, t.gate k i j =
      W (i.1,restrictPayload I (held S k)ᶜ i.2) (j.1,restrictPayload I (held S k)ᶜ j.2) *
        if restrictPayload I (held S k) i.2 = restrictPayload I (held S k) j.2 then 1 else 0 := by
    intro i j
    have hh : restrictPayload I (held S k)ᶜᶜ i.2 = restrictPayload I (held S k)ᶜᶜ j.2 ↔
        restrictPayload I (held S k) i.2 = restrictPayload I (held S k) j.2 := by
      rw [restriction_eq_iff,restriction_eq_iff]
      simp
    simpa only [hh] using hTW i j
  have hT := tester_owned_matrix e r (held S k) (t.gate k) W he
  unfold ownedMarginal
  rw [← evolve_submatrix_equiv,hT]
  simp only [submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply,submatrix_id_id]
  exact partialRight_evolve_one_kron _ _ hW

theorem owned_device_contact {I : Inventory} {S : Schedule I} (e : Extension S)
    (r : ℕ) (k : Cut S) (ρ : Mat (Global e r)) :
    ownedMarginal e r (held S k) (evolve (liftDeviceObservable e r (e.gate k)) ρ) =
      evolve (localContactGate e k) (ownedMarginal e r (held S k) ρ) := by
  have hD := device_owned_matrix e r (held S k) (e.gate k) (localContactGate e k)
    (localContactGate_spec e k).2
  unfold ownedMarginal
  rw [← evolve_submatrix_equiv,hD]
  simp only [submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply,submatrix_id_id]
  exact partialRight_evolve_kron_one _ _

theorem owned_joint_contact {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (ρ : Mat (Global e r)) :
    ownedMarginal e r (held S k) (evolve (jointGate e t k) ρ) =
      evolve (localContactGate e k) (ownedMarginal e r (held S k) ρ) := by
  rw [jointGate_as_product,evolve_mul,owned_tester_invariant,owned_device_contact]

def contactBodyReadout {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S) :
    Mat (Fin e.b × Restricted I (held S k)) →ₗ[ℂ] Mat (Fin e.b) :=
  (partialRightLinear (Fin e.b) (Restricted I (held S k))).comp
    (sandwichLinear (localContactGate e k))

theorem actual_cut_body_readout {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (ρ : Mat (Global e r)) :
    partialRight (evolve (jointGate e t k) ρ) =
      contactBodyReadout e k (ownedMarginal e r (held S k) ρ) := by
  rw [← owned_body_marginal e r (held S k) (evolve (jointGate e t k) ρ),owned_joint_contact]
  rfl

def ownedHistory {I : Inventory} {S : Schedule I} (e : Extension S) {r : ℕ}
    (t : Tester S r) (k : Cut S) : Mat (Fin e.b × Restricted I (held S k)) :=
  ownedMarginal e r (held S k) (run e t k.val)

def finalCut {I : Inventory} (S : Schedule I) : Cut S := ⟨2*S.visits,by omega⟩

theorem bodyOutput_owned_readout {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) :
    bodyOutput e t = contactBodyReadout e (finalCut S) (ownedHistory e t (finalCut S)) := by
  unfold bodyOutput finalState
  rw [run,dif_pos (by omega)]
  exact actual_cut_body_readout e t (finalCut S) _

end ScheduleLaw.History
