import RecordCausality

/-! Exact commutation of the device and observer on their disjoint owned
systems. In particular, a legal tester contact commutes with a held SWAP. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem restriction_eq_iff (I : Inventory) (A : Finset (Fin I.count)) (p q : Payload I) :
    restrictPayload I A p = restrictPayload I A q ↔ ∀ c ∈ A, p c = q c := by
  constructor
  · intro h c hc
    exact congrFun h ⟨c,hc⟩
  · intro h
    funext c
    exact h c.val c.property

def ownershipCoordinates {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) :
    Global e r ≃ (Fin e.b × Restricted I A) × (Fin r × Restricted I Aᶜ) where
  toFun x := ((x.1,restrictPayload I A x.2.1),(x.2.2,restrictPayload I Aᶜ x.2.1))
  invFun x := (x.1.1,((payloadPartition I A).symm (x.1.2,x.2.2),x.2.1))
  left_inv x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (payloadPartition I A).symm_apply_apply x.2.1
      · rfl
  right_inv x := by
    have hp := (payloadPartition I A).apply_symm_apply (x.1.2,x.2.2)
    change ((x.1.1,((payloadPartition I A) ((payloadPartition I A).symm (x.1.2,x.2.2))).1),
      (x.2.1,((payloadPartition I A) ((payloadPartition I A).symm (x.1.2,x.2.2))).2)) = x
    rw [hp]

theorem device_owned_matrix {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (U : Mat (Fin e.b × Payload I))
    (V : Mat (Fin e.b × Restricted I A))
    (he : ∀ i j, U i j = V (i.1,restrictPayload I A i.2) (j.1,restrictPayload I A j.2) *
      if restrictPayload I Aᶜ i.2 = restrictPayload I Aᶜ j.2 then 1 else 0) :
    liftDeviceObservable e r U =
      (V ⊗ₖ (1 : Mat (Fin r × Restricted I Aᶜ))).submatrix
        (ownershipCoordinates e r A) (ownershipCoordinates e r A) := by
  ext i j
  simp only [liftDeviceObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    Equiv.prodAssoc_symm_apply,ownershipCoordinates,Equiv.coe_fn_mk,he,Prod.mk.injEq]
  by_cases hm : i.2.2 = j.2.2 <;>
    by_cases hp : restrictPayload I Aᶜ i.2.1 = restrictPayload I Aᶜ j.2.1 <;> simp [hm,hp]

theorem tester_owned_matrix {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (U : Mat (Fin r × Payload I))
    (V : Mat (Fin r × Restricted I Aᶜ))
    (he : ∀ i j, U i j = V (i.1,restrictPayload I Aᶜ i.2) (j.1,restrictPayload I Aᶜ j.2) *
      if restrictPayload I A i.2 = restrictPayload I A j.2 then 1 else 0) :
    liftTesterObservable e r U =
      ((1 : Mat (Fin e.b × Restricted I A)) ⊗ₖ V).submatrix
        (ownershipCoordinates e r A) (ownershipCoordinates e r A) := by
  ext i j
  simp only [liftTesterObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    Equiv.prodComm_apply,ownershipCoordinates,Equiv.coe_fn_mk,he,Prod.mk.injEq]
  by_cases hb : i.1 = j.1 <;>
    by_cases hp : restrictPayload I A i.2.1 = restrictPayload I A j.2.1 <;> simp [hb,hp]

theorem disjoint_lifts_commute {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (U : Mat (Fin e.b × Payload I))
    (T : Mat (Fin r × Payload I)) (hU : LocalOn I e.b A U) (hT : LocalOn I r Aᶜ T) :
    Commute (liftDeviceObservable e r U) (liftTesterObservable e r T) := by
  obtain ⟨V,hV,hUV⟩ := hU
  obtain ⟨W,hW,hTW⟩ := hT
  have hTW' : ∀ i j, T i j = W (i.1,restrictPayload I Aᶜ i.2) (j.1,restrictPayload I Aᶜ j.2) *
      if restrictPayload I A i.2 = restrictPayload I A j.2 then 1 else 0 := by
    intro i j
    have he : (restrictPayload I Aᶜᶜ i.2 = restrictPayload I Aᶜᶜ j.2) ↔
        (restrictPayload I A i.2 = restrictPayload I A j.2) := by
      rw [restriction_eq_iff,restriction_eq_iff]
      simp
    simpa only [he] using hTW i j
  rw [device_owned_matrix e r A U V hUV,tester_owned_matrix e r A T W hTW']
  change _ * _ = _ * _
  rw [submatrix_mul_equiv,submatrix_mul_equiv,← mul_kronecker_mul,← mul_kronecker_mul]
  simp

/-- This uses the actual tester locality proof, not just unitarity. -/
theorem tester_held_swap_commute {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (k : Cut S) (v : Fin S.visits) (hv : S.carrier v ∈ held S k) :
    Commute ((wire (Recorder.arrivalCut (S := S) v) r).permMatrix ℂ) (testerOperator t k) := by
  have hc := disjoint_lifts_commute (Recorder.extension S) r (held S k)
    ((Recorder.swapFin v).permMatrix ℂ) (t.gate k)
    (Recorder.swapFin_local v _ hv) (t.gate_local k)
  have he := congrArg (fun M : Mat (Global (Recorder.extension S) r) =>
    M.submatrix (actual S r) (actual S r)) hc.eq
  dsimp only at he
  rw [← submatrix_mul_equiv _ _ (actual S r) (actual S r) (actual S r),
    ← submatrix_mul_equiv _ _ (actual S r) (actual S r) (actual S r)] at he
  have hd : (liftDeviceObservable (Recorder.extension S) r ((Recorder.swapFin v).permMatrix ℂ)).submatrix
      (actual S r) (actual S r) = (wire (Recorder.arrivalCut (S := S) v) r).permMatrix ℂ := by
    rw [← Recorder.extension_arrival S v]
    exact device_raw S r _
  rw [hd,testerOperator_actual] at he
  exact he

theorem tester_held_swap_invariant {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (k : Cut S) (v : Fin S.visits) (hv : S.carrier v ∈ held S k) :
    (testerOperator t k).submatrix (wire (Recorder.arrivalCut (S := S) v) r)
      (wire (Recorder.arrivalCut (S := S) v) r) = testerOperator t k := by
  let σ := wire (Recorder.arrivalCut (S := S) v) r
  have hc := tester_held_swap_commute S t k v hv
  rw [← Recorder.permutation_evolve]
  unfold evolve
  rw [hc.eq,mul_assoc,(Recorder.permutation_unitary σ).2,mul_one]

end History
end ScheduleLaw
