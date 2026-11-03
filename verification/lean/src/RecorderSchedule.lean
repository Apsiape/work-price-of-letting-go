import Recorder

/-! Exact schedule and retained-register invariants of the recorder contacts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace Recorder

def contact {I : Inventory} {S : Schedule I} (k : Cut S) :
    Equiv.Perm (Stock S × Payload I) :=
  if h : ∃ v, arrivalCut v = k then swapEquiv (Classical.choose h) else Equiv.refl _

theorem contact_arrival {I : Inventory} {S : Schedule I} (v : Fin S.visits) :
    contact (arrivalCut v) = swapEquiv v := by
  have h : ∃ w, arrivalCut w = arrivalCut v := ⟨v,rfl⟩
  rw [contact,dif_pos h]
  rw [arrivalCut_injective (Classical.choose_spec h)]

theorem contact_partner {I : Inventory} {S : Schedule I} (k : Cut S)
    (x : Stock S × Payload I) : (contact k x).1.2 = x.1.2 := by
  unfold contact
  split_ifs
  · rfl
  · rfl

theorem contact_other_input {I : Inventory} {S : Schedule I} (k : Cut S)
    (v : Fin S.visits) (h : k ≠ arrivalCut v) (x : Stock S × Payload I) :
    (contact k x).1.1 v = x.1.1 v := by
  unfold contact
  split_ifs with hk
  · have hv : v ≠ Classical.choose hk := by
      intro he
      exact h ((Classical.choose_spec hk).symm.trans (congrArg arrivalCut he.symm))
    exact swapAt_other_input _ _ hv x
  · rfl

/-- After its arrival SWAP, the actual physical carrier is left untouched by
every recorder contact until its scheduled release, including interleavings. -/
theorem contact_keeps_held_carrier {I : Inventory} {S : Schedule I} (k : Cut S)
    (v : Fin S.visits)
    (hv : (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val)
    (hnot : k ≠ arrivalCut v) (x : Stock S × Payload I) :
    (contact k x).2 (S.carrier v) = x.2 (S.carrier v) := by
  unfold contact
  split_ifs with hk
  · let w := Classical.choose hk
    have hw : arrivalCut w = k := Classical.choose_spec hk
    have hwactive : (S.position (w,false)).val < k.val ∧ k.val ≤ (S.position (w,true)).val := by
      rw [← hw]
      constructor
      · simp [arrivalCut]
      · exact S.ordered w
    have hne : S.carrier v ≠ S.carrier w := by
      intro hc
      have he := active_visit_unique S k hv hwactive hc
      exact hnot (hw.symm.trans (congrArg arrivalCut he.symm))
    exact swapAt_other_carrier w (S.carrier v) hne x
  · rfl

theorem gate_contact {I : Inventory} {S : Schedule I} (k : Cut S) :
    gate k = (Equiv.Perm.permMatrix ℂ (contact k)).submatrix
      (Equiv.prodCongr (stockFin S).symm (Equiv.refl _))
      (Equiv.prodCongr (stockFin S).symm (Equiv.refl _)) := by
  ext i j
  unfold gate contact
  split_ifs with hk
  · simp only [permutation_entry,submatrix_apply]
    let u := Equiv.prodCongr (stockFin S).symm (Equiv.refl (Payload I))
    have he : swapFin (Classical.choose hk) i = j ↔
        swapEquiv (Classical.choose hk) (u i) = u j := by
      change u.symm (swapEquiv (Classical.choose hk) (u i)) = j ↔ _
      exact u.symm.apply_eq_iff_eq_symm_apply
    simp only [he]
    rfl
  · simp [permutation_entry,one_apply,Prod.ext_iff]

end Recorder
end ScheduleLaw
