import BlueprintKernelPorts
import BlueprintKernelDevice

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

theorem rect_reindex_injective {a b c d : Type} (e : c ≃ a) (f : d ≃ b)
    {A B : Matrix a b ℂ} (h : A.submatrix e f=B.submatrix e f) : A=B := by
  ext i j
  simpa only [submatrix_apply,Equiv.apply_symm_apply] using congrFun₂ h (e.symm i) (f.symm j)

theorem cross_reindex {a b d x y z : Type} [Fintype a] [Fintype y]
    (e : x ≃ b) (f : y ≃ a) (g : z ≃ d)
    (K : Matrix b a ℂ) (L : Matrix d a ℂ) (ρ : Mat a) :
    (K*ρ*Lᴴ).submatrix e g=
      K.submatrix e f*ρ.submatrix f f*(L.submatrix g f)ᴴ := by
  rw [conjTranspose_submatrix,submatrix_mul_equiv,submatrix_mul_equiv]

def routedArrival {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (K : Matrix (b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    Matrix (b × Registers S (insert v V)) (Recorder.Stock S × Registers S (insert v V)) ℂ :=
  heldFromPort V v hv (arrivalKernel (unheldPortKernel V v K))

def routedRelease {I : Inventory} {S : Schedule I} {b : Type}
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (K : Matrix (b × Registers S (insert v V)) (Recorder.Stock S × Registers S (insert v V)) ℂ) :
    Matrix (b × Registers S V) (Recorder.Stock S × Registers S V) ℂ :=
  unheldFromPort V v (releaseKernel (heldPortKernel V v hv K))

theorem routedArrival_cancellation {I : Inventory} {S : Schedule I} {b : Type} (r : ℕ)
    (V : Finset (Fin S.visits)) (v : Fin S.visits) (hv : v ∉ V)
    (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
    (K : Matrix (b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    routedLift r (insert v V) hc (routedArrival V v hv K)*
      (wire (Recorder.arrivalCut (S := S) v) r).permMatrix ℂ=
        routedLift r V (hc.mono (Finset.subset_insert v V)) K := by
  apply rect_reindex_injective (physicalPort S r b V v hv hc).symm (portRaw S r V v hv hc).symm
  rw [← submatrix_mul_equiv _ _ (physicalPort S r b V v hv hc).symm
    (portRaw S r V v hv hc).symm (portRaw S r V v hv hc).symm,
    held_routed_port,port_arrival_matrix,unheld_routed_port]
  simp only [routedArrival,held_roundtrip]
  ext i j
  rw [mul_permutation_entry,arrivalPermutation_symm]
  change unheldPortKernel V v K i.1 j.1 *
      (if i.2.1=j.2.1 then 1 else 0)*(if i.2.2=j.2.2 then 1 else 0)=
    unheldPortKernel V v K i.1 j.1*(if i.2=j.2 then 1 else 0)
  by_cases hp : i.2.1=j.2.1 <;> by_cases hu : i.2.2=j.2.2 <;>
    simp [Prod.ext_iff,hp,hu]


theorem routedRelease_actual_cross {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (v : Fin S.visits) (b d : Type)
    (K : Matrix (b × Registers S (insert v (releaseOthers S v)))
      (Recorder.Stock S × Registers S (insert v (releaseOthers S v))) ℂ)
    (L : Matrix (d × Registers S (insert v (releaseOthers S v)))
      (Recorder.Stock S × Registers S (insert v (releaseOthers S v))) ℂ) :
    routedLift r (insert v (releaseOthers S v)) (releasePorts_injective S v) K*
      rawState t (endpointAfter S v true).val*
        (routedLift r (insert v (releaseOthers S v)) (releasePorts_injective S v) L)ᴴ =
    routedLift r (releaseOthers S v) ((releasePorts_injective S v).mono (Finset.subset_insert _ _))
        (routedRelease (releaseOthers S v) v (releaseOthers_not_mem S v) K)*
      rawState t (endpointAfter S v true).val*
        (routedLift r (releaseOthers S v) ((releasePorts_injective S v).mono (Finset.subset_insert _ _))
          (routedRelease (releaseOthers S v) v (releaseOthers_not_mem S v) L))ᴴ := by
  let V := releaseOthers S v
  let hv := releaseOthers_not_mem S v
  let hc := releasePorts_injective S v
  apply rect_reindex_injective (physicalPort S r b V v hv hc).symm
    (physicalPort S r d V v hv hc).symm
  rw [cross_reindex _ (portRaw S r V v hv hc).symm,
    cross_reindex _ (portRaw S r V v hv hc).symm,
    held_routed_port,held_routed_port,unheld_routed_port,unheld_routed_port]
  simp only [routedRelease,unheld_roundtrip]
  exact actual_release_cross S t v b d _ _

theorem wire_release_identity {I : Inventory} (S : Schedule I) (v : Fin S.visits) (r : ℕ) :
    wire (endpointAfter S v true) r=Equiv.refl _ := by
  have hn : ¬∃ w, Recorder.arrivalCut (S := S) w=endpointAfter S v true := by
    rintro ⟨w,hw⟩
    have he := congrArg Fin.val hw
    have hp : S.position (w,false)=S.position (v,true) := Fin.ext (by
      simpa only [Recorder.arrivalCut,endpointAfter] using Nat.add_right_cancel he)
    have hb := congrArg Prod.snd (S.position.injective hp)
    cases hb
  apply Equiv.ext
  intro x
  rw [wire_apply]
  simp only [Recorder.contact,dif_neg hn,Equiv.refl_apply]

#print axioms rect_reindex_injective
#print axioms cross_reindex
#print axioms routedArrival
#print axioms routedRelease
#print axioms routedArrival_cancellation
#print axioms routedRelease_actual_cross
#print axioms wire_release_identity
end ScheduleLaw.Blueprint
