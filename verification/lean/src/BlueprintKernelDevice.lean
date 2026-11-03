import BlueprintKernelLocal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

def sampledPayload {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (h : Registers S V) : Payload I :=
  (visitPayloadPartition S V hc).symm (h,fun c => ⟨0,I.dim_pos c.val⟩)

theorem sampled_selected {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (h : Registers S V) :
    selectedVisits S V (sampledPayload S V hc h)=h := by
  have he := congrArg Prod.fst ((visitPayloadPartition S V hc).apply_symm_apply
    (h,fun c => ⟨0,I.dim_pos c.val⟩))
  exact he

theorem sampled_outside {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (h : Registers S V) :
    restrictPayload I (visitCarriers S V)ᶜ (sampledPayload S V hc h)=
      (fun c => ⟨0,I.dim_pos c.val⟩) := by
  have he := congrArg Prod.snd ((visitPayloadPartition S V hc).apply_symm_apply
    (h,fun c => ⟨0,I.dim_pos c.val⟩))
  exact he

theorem sampled_owned {I : Inventory} (S : Schedule I) (k : Cut S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (hA : held S k=visitCarriers S V) (p : Payload I) :
    restrictPayload I (held S k) (sampledPayload S V hc (selectedVisits S V p))=
      restrictPayload I (held S k) p := by
  funext c
  have hm : c.val ∈ visitCarriers S V := by rw [← hA]; exact c.property
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
  have hv' := congrFun (sampled_selected S V hc (selectedVisits S V p)) ⟨v,hv⟩
  change sampledPayload S V hc (selectedVisits S V p) (S.carrier v)=p (S.carrier v) at hv'
  rw [he] at hv'
  exact hv'

def routedDeviceGate {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    Mat (Fin e.b × Registers S V) := fun i j =>
  e.gate k (i.1,sampledPayload S V hc i.2) (j.1,sampledPayload S V hc j.2)

theorem routedDeviceGate_spec {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (hA : held S k=visitCarriers S V) (i j : Fin e.b × Payload I) :
    e.gate k i j=routedDeviceGate e k V hc
      (i.1,selectedVisits S V i.2) (j.1,selectedVisits S V j.2) *
      if restrictPayload I (visitCarriers S V)ᶜ i.2=restrictPayload I (visitCarriers S V)ᶜ j.2
        then 1 else 0 := by
  obtain ⟨U,hU,hUV⟩ := e.gate_local k
  have h0 := hUV (i.1,sampledPayload S V hc (selectedVisits S V i.2))
    (j.1,sampledPayload S V hc (selectedVisits S V j.2))
  simp only [sampled_owned S k V hc hA] at h0
  have he : restrictPayload I (held S k)ᶜ (sampledPayload S V hc (selectedVisits S V i.2))=
      restrictPayload I (held S k)ᶜ (sampledPayload S V hc (selectedVisits S V j.2)) := by
    rw [hA,sampled_outside,sampled_outside]
  rw [if_pos he,mul_one] at h0
  rw [hUV i j,← h0]
  rw [hA]
  rfl

theorem routedDevice_lift {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (hA : held S k=visitCarriers S V) (r : ℕ) :
    liftDeviceObservable e r (e.gate k)=routedLift r V hc (routedDeviceGate e k V hc) := by
  ext i j
  rw [routedLift_entry]
  simp only [liftDeviceObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    Equiv.prodAssoc_symm_apply,routedDeviceGate_spec e k V hc hA]
  by_cases hp : restrictPayload I (visitCarriers S V)ᶜ i.2.1=
      restrictPayload I (visitCarriers S V)ᶜ j.2.1 <;>
    by_cases hm : i.2.2=j.2.2 <;> simp [hp,hm]

theorem routedTester_device {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) :
    routedTester (Fin e.b) t k=liftTesterObservable e r (t.gate k) := by
  rfl

theorem routedTester_recorder {I : Inventory} {S : Schedule I}
    {r : ℕ} (t : Tester S r) (k : Cut S) :
    routedTester (Recorder.Stock S) t k=testerOperator t k := by
  ext i j
  simp [routedTester,testerOperator,kroneckerMap_apply,one_apply]

theorem routed_kernel_tester {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (hA : held S k=visitCarriers S V)
    (K : Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    routedLift r V hc K*testerOperator t k=
      liftTesterObservable e r (t.gate k)*routedLift r V hc K := by
  simpa only [routedTester_device,routedTester_recorder] using
    routedLift_tester t k V hc hA K

theorem routed_device_comp {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (hA : held S k=visitCarriers S V)
    (K : Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) (r : ℕ) :
    routedLift r V hc (routedDeviceGate e k V hc*K)=
      liftDeviceObservable e r (e.gate k)*routedLift r V hc K := by
  rw [routedLift_mul,← routedDevice_lift e k V hc hA]

#print axioms sampledPayload
#print axioms sampled_selected
#print axioms sampled_outside
#print axioms sampled_owned
#print axioms routedDeviceGate
#print axioms routedDeviceGate_spec
#print axioms routedDevice_lift
#print axioms routedTester_device
#print axioms routedTester_recorder
#print axioms routed_kernel_tester
#print axioms routed_device_comp
end ScheduleLaw.Blueprint
