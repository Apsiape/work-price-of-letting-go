import DisjointLocality
import Mathlib.Data.Finset.NoncommProd

/-! Commuting simultaneous visit SWAPs and the frame that keeps a selected
family of EPR halves in their original stock coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Function
namespace ScheduleLaw
namespace History

def visitSwap {I : Inventory} (S : Schedule I) (r : ℕ) (v : Fin S.visits) : Equiv.Perm (Raw S r) :=
  wire (Recorder.arrivalCut (S := S) v) r

theorem stock_swaps_commute {I : Inventory} (S : Schedule I) (v w : Fin S.visits)
    (hc : S.carrier v ≠ S.carrier w) (x : Recorder.Stock S × Payload I) :
    Recorder.swapAt v (Recorder.swapAt w x) = Recorder.swapAt w (Recorder.swapAt v x) := by
  have hvw : v ≠ w := fun h => hc (congrArg S.carrier h)
  rcases x with ⟨⟨a,R⟩,p⟩
  apply Prod.ext
  · apply Prod.ext
    · simp only [Recorder.swapAt,Function.update_of_ne hc,Function.update_of_ne hc.symm]
      exact Function.update_comm hvw.symm _ _ _
    · rfl
  · simp only [Recorder.swapAt,Function.update_of_ne hvw,Function.update_of_ne hvw.symm]
    exact Function.update_comm hc.symm _ _ _

theorem visitSwap_commute {I : Inventory} (S : Schedule I) (r : ℕ) (v w : Fin S.visits)
    (hc : S.carrier v ≠ S.carrier w) : Commute (visitSwap S r v) (visitSwap S r w) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,visitSwap,wire_apply,Recorder.contact_arrival]
  change ((Recorder.swapAt v (Recorder.swapAt w (x.1,x.2.1))).1,
    ((Recorder.swapAt v (Recorder.swapAt w (x.1,x.2.1))).2,x.2.2)) =
    ((Recorder.swapAt w (Recorder.swapAt v (x.1,x.2.1))).1,
      ((Recorder.swapAt w (Recorder.swapAt v (x.1,x.2.1))).2,x.2.2))
  rw [stock_swaps_commute S v w hc]

theorem visitSwap_square {I : Inventory} (S : Schedule I) (r : ℕ) (v : Fin S.visits) :
    visitSwap S r v * visitSwap S r v = 1 := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,visitSwap,wire_apply,Recorder.contact_arrival]
  change ((Recorder.swapAt v (Recorder.swapAt v (x.1,x.2.1))).1,
    ((Recorder.swapAt v (Recorder.swapAt v (x.1,x.2.1))).2,x.2.2)) = x
  rw [Recorder.swapAt_involutive v]

theorem visitSwap_pairwise {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits))) :
    (J : Set (Fin S.visits)).Pairwise (Commute on visitSwap S r) := by
  intro v hv w hw hvw
  exact visitSwap_commute S r v w (fun he => hvw (hc hv hw he))

def gauge {I : Inventory} (S : Schedule I) (r : ℕ) (J : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (J : Set (Fin S.visits))) : Equiv.Perm (Raw S r) :=
  J.noncommProd (visitSwap S r) (visitSwap_pairwise S r J hc)

theorem gauge_empty {I : Inventory} (S : Schedule I) (r : ℕ)
    (hc : Set.InjOn S.carrier ((∅ : Finset (Fin S.visits)) : Set (Fin S.visits))) : gauge S r ∅ hc = 1 := by
  simp [gauge]

theorem gauge_insert {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ J)
    (hc : Set.InjOn S.carrier ((insert v J : Finset (Fin S.visits)) : Set (Fin S.visits))) :
    gauge S r (insert v J) hc = visitSwap S r v *
      gauge S r J (hc.mono (by intro w hw; exact Finset.mem_insert_of_mem hw)) := by
  exact Finset.noncommProd_insert_of_notMem J v (visitSwap S r) _ hv

theorem gauge_commute_swap {I : Inventory} (S : Schedule I) (r : ℕ)
    (J : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (v : Fin S.visits) (hv : ∀ w ∈ J, S.carrier v ≠ S.carrier w) :
    Commute (visitSwap S r v) (gauge S r J hc) :=
  Finset.noncommProd_commute J (visitSwap S r) _ _ (fun w hw => visitSwap_commute S r v w (hv w hw))

theorem tester_gauge_invariant {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (k : Cut S) (J : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (J : Set (Fin S.visits)))
    (hh : ∀ v ∈ J, S.carrier v ∈ held S k) :
    (testerOperator t k).submatrix (gauge S r J hc) (gauge S r J hc) = testerOperator t k := by
  apply Finset.noncommProd_induction J (visitSwap S r) (visitSwap_pairwise S r J hc)
    (fun σ => (testerOperator t k).submatrix σ σ = testerOperator t k)
  · intro σ τ hσ hτ
    change ((testerOperator t k).submatrix σ σ).submatrix τ τ = testerOperator t k
    rw [hσ,hτ]
  · rfl
  · intro v hv
    exact tester_held_swap_invariant S t k v (hh v hv)

end History
end ScheduleLaw
