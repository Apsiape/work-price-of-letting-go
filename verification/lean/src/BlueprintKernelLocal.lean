import BlueprintKernelBase

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

def selectedVisits {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (p : Payload I) : Registers S V := fun v => p (S.carrier v.val)

theorem selectedVisits_eq_iff {I : Inventory} (S : Schedule I)
    (V : Finset (Fin S.visits)) (p q : Payload I) :
    selectedVisits S V p=selectedVisits S V q ↔
      restrictPayload I (visitCarriers S V) p=restrictPayload I (visitCarriers S V) q := by
  rw [restriction_eq_iff]
  constructor
  · intro h c hc
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
    exact congrFun h ⟨v,hv⟩
  · intro h
    funext v
    exact h _ (Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩)

def routedFrame {I : Inventory} (S : Schedule I) (a : Type) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    a × (Payload I × Fin r) ≃ (a × Registers S V) × (Restricted I (visitCarriers S V)ᶜ × Fin r) where
  toFun x := ((x.1,(visitPayloadPartition S V hc x.2.1).1),
    ((visitPayloadPartition S V hc x.2.1).2,x.2.2))
  invFun x := (x.1.1,((visitPayloadPartition S V hc).symm (x.1.2,x.2.1),x.2.2))
  left_inv x := by simp
  right_inv x := by simp

def routedLift {I : Inventory} {S : Schedule I} {a b : Type} (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (K : Matrix (b × Registers S V) (a × Registers S V) ℂ) :
    Matrix (b × (Payload I × Fin r)) (a × (Payload I × Fin r)) ℂ :=
  (K ⊗ₖ (1 : Mat (Restricted I (visitCarriers S V)ᶜ × Fin r))).submatrix
    (routedFrame S b r V hc) (routedFrame S a r V hc)

theorem routed_selected {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (p : Payload I) :
    (visitPayloadPartition S V hc p).1=selectedVisits S V p := by rfl

theorem routed_outside {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (p : Payload I) :
    (visitPayloadPartition S V hc p).2=restrictPayload I (visitCarriers S V)ᶜ p := by rfl

theorem routedLift_entry {I : Inventory} {S : Schedule I} {a b : Type} (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (K : Matrix (b × Registers S V) (a × Registers S V) ℂ)
    (i : b × (Payload I × Fin r)) (j : a × (Payload I × Fin r)) :
    routedLift r V hc K i j = K (i.1,selectedVisits S V i.2.1) (j.1,selectedVisits S V j.2.1) *
      if restrictPayload I (visitCarriers S V)ᶜ i.2.1=restrictPayload I (visitCarriers S V)ᶜ j.2.1 ∧
        i.2.2=j.2.2 then 1 else 0 := by
  simp only [routedLift,submatrix_apply,kroneckerMap_apply,one_apply,routedFrame,
    Equiv.coe_fn_mk,routed_selected,routed_outside,Prod.mk.injEq]

theorem routedLift_mul {I : Inventory} {S : Schedule I} {a b c : Type}
    [Fintype b] (r : ℕ) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (K : Matrix (c × Registers S V) (b × Registers S V) ℂ)
    (L : Matrix (b × Registers S V) (a × Registers S V) ℂ) :
    routedLift r V hc (K*L)=routedLift r V hc K*routedLift r V hc L := by
  rw [routedLift,routedLift,routedLift,submatrix_mul_equiv,← mul_kronecker_mul,one_mul]

theorem held_active_image {I : Inventory} (S : Schedule I) (k : Cut S) :
    held S k=visitCarriers S (activeVisits S k) := by
  ext c
  simp only [held,visitCarriers,activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨v,hv,ha,hr⟩; exact ⟨v,⟨ha,hr⟩,hv⟩
  · rintro ⟨v,⟨ha,hr⟩,hv⟩; exact ⟨v,hv,ha,hr⟩

def cutFromRouted {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) (hA : held S k=visitCarriers S V)
    (K : Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) : CutKernel e k :=
  fun i j => K (i.1,fun v => i.2 ⟨S.carrier v.val,by rw [hA]; exact Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩)
    (j.1,fun v => j.2 ⟨S.carrier v.val,by rw [hA]; exact Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩)

theorem cutFromRouted_lift {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (hA : held S k=visitCarriers S V)
    (K : Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) (r : ℕ) :
    kernelLift e k r (cutFromRouted e k V hA K)=routedLift r V hc K := by
  ext i j
  rw [routedLift_entry]
  unfold kernelLift cutFromRouted
  change K (i.1,selectedVisits S V i.2.1) (j.1,selectedVisits S V j.2.1)*_= _
  rw [hA]

def routedTester {I : Inventory} {S : Schedule I} (a : Type) [DecidableEq a]
    {r : ℕ} (t : Tester S r) (k : Cut S) : Mat (a × (Payload I × Fin r)) :=
  (1 : Mat a) ⊗ₖ (t.gate k).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)

theorem routedTester_frame {I : Inventory} {S : Schedule I} (a : Type) [DecidableEq a]
    {r : ℕ} (t : Tester S r) (k : Cut S) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hA : held S k=visitCarriers S V) :
    ∃ W : Mat (Restricted I (visitCarriers S V)ᶜ × Fin r),
      routedTester a t k=((1 : Mat (a × Registers S V)) ⊗ₖ W).submatrix
        (routedFrame S a r V hc) (routedFrame S a r V hc) := by
  have ht := t.gate_local k
  rw [hA] at ht
  obtain ⟨W,hW,hTW⟩ := ht
  refine ⟨W.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _),?_⟩
  have hh (p q : Payload I) : restrictPayload I (visitCarriers S V)ᶜᶜ p =
      restrictPayload I (visitCarriers S V)ᶜᶜ q ↔ selectedVisits S V p=selectedVisits S V q := by
    rw [compl_compl,selectedVisits_eq_iff]
  ext i j
  simp only [routedTester,submatrix_apply,kroneckerMap_apply,one_apply,
    Equiv.prodComm_apply,routedFrame,Equiv.coe_fn_mk,routed_selected,routed_outside,hTW,hh,Prod.mk.injEq]
  by_cases hb : i.1=j.1 <;> by_cases hp : selectedVisits S V i.2.1=selectedVisits S V j.2.1 <;>
    simp [hb,hp]

theorem routedLift_tester {I : Inventory} {S : Schedule I} {a b : Type}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {r : ℕ} (t : Tester S r) (k : Cut S) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hA : held S k=visitCarriers S V)
    (K : Matrix (b × Registers S V) (a × Registers S V) ℂ) :
    routedLift r V hc K*routedTester a t k=routedTester b t k*routedLift r V hc K := by
  have hloc := t.gate_local k
  rw [hA] at hloc
  obtain ⟨U,hU,hTU⟩ := hloc
  let E := U.submatrix (Equiv.prodComm (Restricted I (visitCarriers S V)ᶜ) (Fin r))
    (Equiv.prodComm _ _)
  have hframe (z : Type) [DecidableEq z] : routedTester z t k=
      ((1 : Mat (z × Registers S V)) ⊗ₖ E).submatrix
        (routedFrame S z r V hc) (routedFrame S z r V hc) := by
    ext i j
    have hh (p q : Payload I) : restrictPayload I (visitCarriers S V)ᶜᶜ p =
        restrictPayload I (visitCarriers S V)ᶜᶜ q ↔ selectedVisits S V p=selectedVisits S V q := by
      rw [compl_compl,selectedVisits_eq_iff]
    simp only [routedTester,E,submatrix_apply,kroneckerMap_apply,one_apply,
      Equiv.prodComm_apply,routedFrame,Equiv.coe_fn_mk,routed_selected,routed_outside,hTU,hh,Prod.mk.injEq]
    by_cases hb : i.1=j.1 <;> by_cases hp : selectedVisits S V i.2.1=selectedVisits S V j.2.1 <;>
      simp [hb,hp]
  rw [hframe a,hframe b,routedLift,submatrix_mul_equiv,submatrix_mul_equiv,
    kernel_external_interchange]

#print axioms selectedVisits
#print axioms selectedVisits_eq_iff
#print axioms routedFrame
#print axioms routedLift
#print axioms routed_selected
#print axioms routed_outside
#print axioms routedLift_entry
#print axioms routedLift_mul
#print axioms held_active_image
#print axioms cutFromRouted
#print axioms cutFromRouted_lift
#print axioms routedTester
#print axioms routedTester_frame
#print axioms routedLift_tester
end ScheduleLaw.Blueprint
