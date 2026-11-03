import HeldSchedule

/-! The fixed SWAP frame selects the actual physical held carrier halves,
not substitute output wires. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem gauge_preserves_input {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (v : Fin S.visits) (hv : v ∉ J) (x : Raw S r) : (gauge S r J hc x).1.1 v = x.1.1 v := by
  apply Finset.noncommProd_induction J (visitSwap S r) (visitSwap_pairwise S r J hc)
    (fun σ => ∀ x : Raw S r, (σ x).1.1 v = x.1.1 v)
  · intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  · intro x; rfl
  · intro w hw x
    have hne : v ≠ w := fun he => hv (he.symm ▸ hw)
    rw [visitSwap,wire_apply,Recorder.contact_arrival]
    exact Recorder.swapAt_other_input w v hne (x.1,x.2.1)

theorem gauge_preserves_carrier {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (c : Fin I.count) (hh : ∀ w ∈ J, c ≠ S.carrier w) (x : Raw S r) :
    (gauge S r J hc x).2.1 c = x.2.1 c := by
  apply Finset.noncommProd_induction J (visitSwap S r) (visitSwap_pairwise S r J hc)
    (fun σ => ∀ x : Raw S r, (σ x).2.1 c = x.2.1 c)
  · intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  · intro x; rfl
  · intro w hw x
    rw [visitSwap,wire_apply,Recorder.contact_arrival]
    exact Recorder.swapAt_other_carrier w c (hh w hw) (x.1,x.2.1)

theorem gauge_preserves_partners {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits))) (x : Raw S r) :
    (gauge S r J hc x).1.2 = x.1.2 := by
  apply Finset.noncommProd_induction J (visitSwap S r) (visitSwap_pairwise S r J hc)
    (fun σ => ∀ x : Raw S r, (σ x).1.2 = x.1.2)
  · intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  · intro x; rfl
  · intro w hw x
    rw [visitSwap,wire_apply,Recorder.contact_arrival]
    rfl

theorem gauge_preserves_memory {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits))) (x : Raw S r) :
    (gauge S r J hc x).2.2 = x.2.2 := by
  apply Finset.noncommProd_induction J (visitSwap S r) (visitSwap_pairwise S r J hc)
    (fun σ => ∀ x : Raw S r, (σ x).2.2 = x.2.2)
  · intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  · intro x; rfl
  · intro w hw x
    rfl

theorem gauge_erase {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (v : Fin S.visits) (hv : v ∈ J) :
    gauge S r J hc = visitSwap S r v *
      gauge S r (J.erase v) (hc.mono (Finset.erase_subset _ _)) := by
  exact (Finset.mul_noncommProd_erase J hv (visitSwap S r) _).symm

theorem gauge_input_mem {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (v : Fin S.visits) (hv : v ∈ J) (x : Raw S r) :
    (gauge S r J hc x).1.1 v = x.2.1 (S.carrier v) := by
  rw [gauge_erase S r J hc v hv]
  simp only [Equiv.Perm.mul_apply,visitSwap,wire_apply,Recorder.contact_arrival]
  change (Recorder.swapAt v _).1.1 v = _
  rw [Recorder.swapAt_input]
  change (gauge S r (J.erase v) _ x).2.1 (S.carrier v) = _
  apply gauge_preserves_carrier S r (J.erase v) _ (S.carrier v) _ x
  intro w hw he
  exact (Finset.mem_erase.mp hw).1 (hc (Finset.mem_of_mem_erase hw) hv he.symm)

theorem gauge_payload_mem {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (v : Fin S.visits) (hv : v ∈ J) (x : Raw S r) :
    (gauge S r J hc x).2.1 (S.carrier v) = x.1.1 v := by
  rw [gauge_erase S r J hc v hv]
  simp only [Equiv.Perm.mul_apply,visitSwap,wire_apply,Recorder.contact_arrival]
  change (Recorder.swapAt v _).2 (S.carrier v) = _
  rw [Recorder.swapAt_payload]
  change (gauge S r (J.erase v) _ x).1.1 v = _
  exact gauge_preserves_input S r (J.erase v) _ v (Finset.notMem_erase _ _) x

theorem gauge_involutive {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits))) :
    Function.Involutive (gauge S r J hc) := by
  intro x
  apply Prod.ext
  · apply Prod.ext
    · funext v
      by_cases hv : v ∈ J
      · rw [gauge_input_mem S r J hc v hv,gauge_payload_mem S r J hc v hv]
      · rw [gauge_preserves_input S r J hc v hv,gauge_preserves_input S r J hc v hv]
    · rw [gauge_preserves_partners,gauge_preserves_partners]
  · apply Prod.ext
    · funext c
      by_cases hv : ∃ v ∈ J, S.carrier v = c
      · obtain ⟨v,hv,rfl⟩ := hv
        rw [gauge_payload_mem S r J hc v hv,gauge_input_mem S r J hc v hv]
      · have hn : ∀ w ∈ J, c ≠ S.carrier w := by
          intro w hw he
          exact hv ⟨w,hw,he.symm⟩
        rw [gauge_preserves_carrier S r J hc c hn,gauge_preserves_carrier S r J hc c hn]
    · rw [gauge_preserves_memory,gauge_preserves_memory]

theorem gauge_symm {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits))) :
    (gauge S r J hc).symm = gauge S r J hc := by
  apply Equiv.ext
  intro x
  apply (gauge S r J hc).injective
  rw [Equiv.apply_symm_apply,gauge_involutive S r J hc]

def heldCoordinates {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    Raw S r ≃ Record S V V × (Record S Vᶜ Vᶜ × (Payload I × Fin r)) :=
  (gauge S r V hc).trans (recordCoordinates S r V V)

theorem heldCoordinates_halves {I : Inventory} (S : Schedule I) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (x : Raw S r) :
    (heldCoordinates S r V hc x).1 =
      ((fun v : {v // v ∈ V} => x.2.1 (S.carrier v.val)),
        fun v : {v // v ∈ V} => x.1.2 v.val) := by
  apply Prod.ext
  · funext v
    change (gauge S r V hc x).1.1 v.val = _
    exact gauge_input_mem S r V hc v.val v.property x
  · funext v
    change (gauge S r V hc x).1.2 v.val = _
    rw [gauge_preserves_partners]

end History
end ScheduleLaw
