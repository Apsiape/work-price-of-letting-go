import TerminalRecord

/-! Exact no-signalling for previously recorded inputs, against every tester. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def rawMarginal {I : Inventory} (S : Schedule I) (r : ℕ)
    (A O : Finset (Fin S.visits)) (ρ : Mat (Raw S r)) : Mat (Record S A O) :=
  partialRight (ρ.submatrix (recordCoordinates S r A O).symm (recordCoordinates S r A O).symm)

theorem rawMarginal_body {I : Inventory} (S : Schedule I) (r : ℕ)
    (A O : Finset (Fin S.visits)) (ρ : Mat (Raw S r)) :
    rawMarginal S r A O ρ = partialRight
      ((partialRight ρ).submatrix (stockPartition S A O).symm (stockPartition S A O).symm) := by
  ext i j
  change (∑ z : Record S Aᶜ Oᶜ × (Payload I × Fin r),
    ρ ((stockPartition S A O).symm (i,z.1),z.2)
      ((stockPartition S A O).symm (j,z.1),z.2)) =
    ∑ q : Record S Aᶜ Oᶜ, ∑ z : Payload I × Fin r,
      ρ ((stockPartition S A O).symm (i,q),z) ((stockPartition S A O).symm (j,q),z)
  exact Fintype.sum_prod_type _

theorem chi_rawMarginal {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (n : ℕ) (A O : Finset (Fin S.visits)) :
    chi t n A O = rawMarginal S r A O
      ((run (Recorder.extension S) t n).submatrix (actual S r) (actual S r)) := rfl

theorem marginal_permutation {x h z : Type} [Fintype x] [Fintype h] [Fintype z]
    (p : x ≃ h × z) (σ : Equiv.Perm x) (τ : Equiv.Perm z)
    (hr : ∀ a, p (σ a) = ((p a).1,τ (p a).2)) (ρ : Mat x) :
    partialRight ((ρ.submatrix σ σ).submatrix p.symm p.symm) =
      partialRight (ρ.submatrix p.symm p.symm) := by
  have he (i : h) (k : z) : σ (p.symm (i,k)) = p.symm (i,τ k) := by
    apply p.injective
    rw [hr]
    simp
  ext i j
  simp only [partialRight,submatrix_apply,he]
  exact Equiv.sum_comp τ (fun k => ρ (p.symm (i,k)) (p.symm (j,k)))

def complementSwap {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (A O : Finset (Fin S.visits)) (hv : v ∉ A) (r : ℕ)
    (x : Record S Aᶜ Oᶜ × (Payload I × Fin r)) : Record S Aᶜ Oᶜ × (Payload I × Fin r) :=
  ((Function.update x.1.1 ⟨v,Finset.mem_compl.mpr hv⟩ (x.2.1 (S.carrier v)),x.1.2),
    (Function.update x.2.1 (S.carrier v) (x.1.1 ⟨v,Finset.mem_compl.mpr hv⟩),x.2.2))

theorem complementSwap_involutive {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (A O : Finset (Fin S.visits)) (hv : v ∉ A) (r : ℕ) :
    Function.Involutive (complementSwap v A O hv r) := by
  rintro ⟨⟨a,o⟩,p,m⟩
  apply Prod.ext
  · apply Prod.ext
    · funext w
      by_cases he : w = ⟨v,Finset.mem_compl.mpr hv⟩
      · subst w; simp [complementSwap]
      · simp [complementSwap,Function.update_of_ne he]
    · rfl
  · apply Prod.ext
    · funext c
      by_cases he : c = S.carrier v
      · subst c; simp [complementSwap]
      · simp [complementSwap,Function.update_of_ne he]
    · rfl

theorem record_wire_route {I : Inventory} (S : Schedule I) (r : ℕ)
    (v : Fin S.visits) (A O : Finset (Fin S.visits)) (hv : v ∉ A) (x : Raw S r) :
    recordCoordinates S r A O (wire (Recorder.arrivalCut (S := S) v) r x) =
      ((recordCoordinates S r A O x).1,
        complementSwap v A O hv r (recordCoordinates S r A O x).2) := by
  have hdefs : wire (Recorder.arrivalCut (S := S) v) r x =
      ((Function.update x.1.1 v (x.2.1 (S.carrier v)),x.1.2),
        (Function.update x.2.1 (S.carrier v) (x.1.1 v),x.2.2)) := by
    rw [wire_apply,Recorder.contact_arrival]
    rfl
  rw [hdefs]
  apply Prod.ext
  · apply Prod.ext
    · funext w
      have hw : w.val ≠ v := by intro he; exact hv (he ▸ w.property)
      simp [recordCoordinates,stockPartition,registerPartition,Prod.map,
        complementSwap,Function.update_of_ne hw]
    · rfl
  · apply Prod.ext
    · apply Prod.ext
      · funext w
        by_cases he : w.val = v
        · have hew : w = ⟨v,Finset.mem_compl.mpr hv⟩ := Subtype.ext he
          subst w
          simp [recordCoordinates,stockPartition,registerPartition,Prod.map,complementSwap]
        · have hew : w ≠ ⟨v,Finset.mem_compl.mpr hv⟩ := fun h => he (congrArg Subtype.val h)
          simp [recordCoordinates,stockPartition,registerPartition,Prod.map,complementSwap,
            Function.update_of_ne he,Function.update_of_ne hew]
      · rfl
    · rfl

theorem rawMarginal_arrival {I : Inventory} (S : Schedule I) (r : ℕ)
    (v : Fin S.visits) (A O : Finset (Fin S.visits)) (hv : v ∉ A) (ρ : Mat (Raw S r)) :
    rawMarginal S r A O (ρ.submatrix (wire (Recorder.arrivalCut (S := S) v) r)
      (wire (Recorder.arrivalCut (S := S) v) r)) = rawMarginal S r A O ρ := by
  exact marginal_permutation (recordCoordinates S r A O) (wire (Recorder.arrivalCut (S := S) v) r)
    ((complementSwap_involutive v A O hv r).toPerm) (record_wire_route S r v A O hv) ρ

def testerOperator {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (k : Cut S) : Mat (Raw S r) :=
  (1 : Mat (Recorder.Stock S)) ⊗ₖ ((t.gate k).submatrix (Equiv.prodComm (Payload I) (Fin r))
    (Equiv.prodComm (Payload I) (Fin r)))

theorem testerOperator_actual {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S) :
    (liftTesterObservable (Recorder.extension S) r (t.gate k)).submatrix (actual S r) (actual S r) =
      testerOperator t k := by
  ext i j
  rw [tester_raw_entry]
  rfl

theorem testerOperator_preserves_record {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S) (A O : Finset (Fin S.visits)) (ρ : Mat (Raw S r)) :
    rawMarginal S r A O (evolve (testerOperator t k) ρ) = rawMarginal S r A O ρ := by
  rw [rawMarginal_body,rawMarginal_body]
  unfold testerOperator
  rw [partialRight_evolve_one_kron _ _
    (unitary_submatrix (Equiv.prodComm (Payload I) (Fin r)) (t.unitary k))]

theorem raw_joint_record {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S) (A O : Finset (Fin S.visits)) (ρ : Mat (Raw S r)) :
    rawMarginal S r A O (evolve
      ((jointGate (Recorder.extension S) t k).submatrix (actual S r) (actual S r)) ρ) =
      rawMarginal S r A O (ρ.submatrix (wire k r) (wire k r)) := by
  rw [jointGate_as_product,
    ← submatrix_mul_equiv _ _ (actual S r) (actual S r) (actual S r),device_raw,
    testerOperator_actual,evolve_mul,testerOperator_preserves_record,Recorder.permutation_evolve]

theorem chi_step_old_inputs {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) (A O : Finset (Fin S.visits))
    (hA : ∀ v, (Recorder.arrivalCut (S := S) v).val = n → v ∉ A) :
    chi t (n+1) A O = chi t n A O := by
  by_cases hn : n < 2*S.visits+1
  · rw [chi_rawMarginal,chi_rawMarginal,run,dif_pos hn,
      ← evolve_submatrix_equiv (actual S r),raw_joint_record]
    by_cases hk : ∃ v, Recorder.arrivalCut (S := S) v = (⟨n,hn⟩ : Cut S)
    · obtain ⟨v,hv⟩ := hk
      rw [← hv]
      exact rawMarginal_arrival S r v A O (hA v (congrArg Fin.val hv)) _
    · have hw : wire (⟨n,hn⟩ : Cut S) r = Equiv.refl _ := by
        apply Equiv.ext
        intro x
        rw [wire_apply]
        have hc : Recorder.contact (⟨n,hn⟩ : Cut S) = Equiv.refl _ := by
          simp only [Recorder.contact,dif_neg hk]
        rw [hc]
        rfl
      rw [hw]
      rfl
  · rw [chi_rawMarginal,chi_rawMarginal,run,dif_neg hn]

/-- Once an input register has been recorded, its joint marginal with any
retained partners is unaffected by all later contacts and tester operations. -/
theorem recorded_inputs_frozen {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (m n : ℕ) (hmn : m ≤ n) (O : Finset (Fin S.visits)) :
    chi t n (arrived S m) O = chi t m (arrived S m) O := by
  induction n,hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [chi_step_old_inputs S t n]
    · exact ih
    · intro v hv hmem
      have ha := (Finset.mem_filter.mp hmem).2
      change (S.position (v,false)).val+1 = n at hv
      omega

end History
end ScheduleLaw
