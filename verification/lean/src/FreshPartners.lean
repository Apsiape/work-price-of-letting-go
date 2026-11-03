import FreshHeld
import RegisterRefinement

/-! Tracing the physical halves leaves flat partners, independent of all
remaining physical registers, including the tester reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem partialLeft_assoc_kron {a b c : Type} [Fintype a]
    (A : Mat (a × b)) (B : Mat c) :
    partialLeft ((A ⊗ₖ B).submatrix (Equiv.prodAssoc a b c).symm
      (Equiv.prodAssoc a b c).symm) = partialLeft A ⊗ₖ B := by
  ext i j
  change (∑ k, A (k,i.1) (k,j.1) * B i.2 j.2) =
    (∑ k, A (k,i.1) (k,j.1)) * B i.2 j.2
  exact (Finset.sum_mul _ _ _).symm

theorem epr_left_reduction {a : Type} [Fintype a] [DecidableEq a] [Nonempty a] :
    partialLeft (pureMatrix (Recorder.epr (a := a))) =
      (Fintype.card a : ℂ)⁻¹ • (1 : Mat a) := by
  have he : partialLeft (pureMatrix (Recorder.epr (a := a))) =
      partialRight (pureMatrix (Recorder.epr (a := a))) := by
    ext i j
    apply Finset.sum_congr rfl
    intro k hk
    simp only [pureMatrix,Recorder.epr,eq_comm]
  rw [he,Recorder.epr_reduction]
  ext i j
  simp only [diagonal_apply,smul_apply,one_apply,smul_eq_mul]
  split_ifs <;> simp_all

def partnerRest {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (K : Cut S)
    (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    Mat (Registers S V × (Record S Vᶜ Vᶜ × (Payload I × Fin r))) :=
  partialLeft ((heldState S t K V hV).submatrix
    (Equiv.prodAssoc (Registers S V) (Registers S V) _).symm
    (Equiv.prodAssoc (Registers S V) (Registers S V) _).symm)

/-- The trace is over exactly the actual held physical halves, as identified
by heldCoordinates_halves, retaining the partners and the complete rest. -/
theorem fresh_partners_flat {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S K) :
    partnerRest S t K V hV =
      ((outputDimension S V : ℂ)⁻¹ • (1 : Mat (Registers S V))) ⊗ₖ
        partialLeft (heldState S t K V hV) := by
  unfold partnerRest
  nth_rw 1 [fresh_held_pair_factor]
  rw [partialLeft_assoc_kron,epr_left_reduction,registers_card]

end History
end ScheduleLaw
