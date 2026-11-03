import BlueprintKernelTransitions

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

def KernelAt {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (V : Finset (Fin S.visits)) : Prop :=
  ∃ (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (K : Fin e.f → Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ),
    ∀ (r : ℕ) (t : Tester S r) (f g : Fin e.f), sourceBlock e t (k.val+1) f g=
      routedLift r V hc (K f)*rawState t (k.val+1)*(routedLift r V hc (K g))ᴴ

theorem kernelAt_initial {I : Inventory} {S : Schedule I} (e : Extension S) :
    KernelAt e ⟨0,by omega⟩ (activeVisits S ⟨0,by omega⟩) := by
  let k : Cut S := ⟨0,by omega⟩
  let V := activeVisits S k
  let hc := activeVisits_carriers_injective S k V (Finset.Subset.refl _)
  let K := fun (f : Fin e.f) (i : Fin e.b × Registers S V)
    (j : Recorder.Stock S × Registers S V) => initialResponse e f i.1 j.1
  refine ⟨hc,K,?_⟩
  intro r t f g
  have hL (f : Fin e.f) : routedLift r V hc (K f)=kernelLift e k r (initialCutKernel e f) := by
    rw [← cutFromRouted_lift e k V hc (held_active_image S k)]
    rfl
  rw [hL,hL]
  exact initial_kernel_contraction e r t f g

theorem kernelAt_arrival {I : Inventory} {S : Schedule I} (e : Extension S) (v : Fin S.visits)
    (hp : KernelAt e (endpointBefore S v false) (activeVisits S (endpointBefore S v false))) :
    KernelAt e (endpointAfter S v false) (insert v (activeVisits S (endpointBefore S v false))) := by
  let V := activeVisits S (endpointBefore S v false)
  have hv : v ∉ V := by simp [V,activeVisits,endpointBefore]
  have hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)) := by
    rw [← active_arrival_update]
    exact activeVisits_carriers_injective S _ _ (Finset.Subset.refl _)
  have hA : held S (endpointAfter S v false)=visitCarriers S (insert v V) := by
    rw [held_active_image,active_arrival_update]
  obtain ⟨hcP,K,hK⟩ := hp
  let k := endpointAfter S v false
  let P := fun f => routedArrival V v hv (K f)
  let Q := fun f => routedDeviceGate e k (insert v V) hc*P f
  refine ⟨hc,Q,?_⟩
  intro r t f g
  let D := liftDeviceObservable e r (e.gate k)
  let T := liftTesterObservable e r (t.gate k)
  let U := testerOperator t k
  have hL (f : Fin e.f) : routedLift r (insert v V) hc (Q f)=
      D*routedLift r (insert v V) hc (P f) := routed_device_comp e k _ hc hA _ r
  have hN (f : Fin e.f) : (D*routedLift r (insert v V) hc (P f))*U=
      T*(D*routedLift r (insert v V) hc (P f)) := by
    rw [← hL]
    exact routed_kernel_tester e t k _ hc hA _
  have hC (f : Fin e.f) : routedLift r (insert v V) hc (P f)*(wire k r).permMatrix ℂ=
      routedLift r V hcP (K f) := routedArrival_cancellation r V v hv hc (K f)
  have hprev : sourceBlock e t k.val f g=
      routedLift r V hcP (K f)*rawState t k.val*(routedLift r V hcP (K g))ᴴ := by
    simpa only [k,endpointBefore,endpointAfter] using hK r t f g
  rw [sourceBlock_step e t k.val k.isLt,jointGate_as_product]
  change evolve (T*D) (sourceBlock e t k.val f g)=
    routedLift r (insert v V) hc (Q f)*rawState t (k.val+1)*(routedLift r (insert v V) hc (Q g))ᴴ
  rw [hprev,hL,hL,rawState_step S t k.val k.isLt]
  exact (arrival_cross_evolution _ _ _ _ D T U ((wire k r).permMatrix ℂ)
    (hC f) (hC g) (hN f) (hN g) (rawState t k.val)).symm

theorem kernelAt_release {I : Inventory} {S : Schedule I} (e : Extension S) (v : Fin S.visits)
    (hp : KernelAt e (endpointBefore S v true) (insert v (releaseOthers S v))) :
    KernelAt e (endpointAfter S v true) (releaseOthers S v) := by
  let V := releaseOthers S v
  let hv := releaseOthers_not_mem S v
  let hc := (releasePorts_injective S v).mono (Finset.subset_insert v V)
  have hA : held S (endpointAfter S v true)=visitCarriers S V := by
    rw [held_active_image,active_release_update]
    rfl
  obtain ⟨hcP,K,hK⟩ := hp
  let k := endpointAfter S v true
  let P := fun f => routedRelease V v hv (K f)
  let Q := fun f => routedDeviceGate e k V hc*P f
  refine ⟨hc,Q,?_⟩
  intro r t f g
  let D := liftDeviceObservable e r (e.gate k)
  let T := liftTesterObservable e r (t.gate k)
  let U := testerOperator t k
  have hL (f : Fin e.f) : routedLift r V hc (Q f)=D*routedLift r V hc (P f) :=
    routed_device_comp e k V hc hA _ r
  have hN (f : Fin e.f) : (D*routedLift r V hc (P f))*U=
      T*(D*routedLift r V hc (P f)) := by
    rw [← hL]
    exact routed_kernel_tester e t k V hc hA _
  have hρ : routedLift r V hc (P f)*rawState t k.val*(routedLift r V hc (P g))ᴴ=
      routedLift r (insert v V) hcP (K f)*rawState t k.val*
        (routedLift r (insert v V) hcP (K g))ᴴ :=
    (routedRelease_actual_cross S t v (Fin e.b) (Fin e.b) (K f) (K g)).symm
  have hraw : rawState t (k.val+1)=evolve U (rawState t k.val) := by
    rw [rawState_step S t k.val k.isLt,wire_release_identity,Matrix.permMatrix_refl,mul_one]
  have hprev : sourceBlock e t k.val f g=
      routedLift r (insert v V) hcP (K f)*rawState t k.val*
        (routedLift r (insert v V) hcP (K g))ᴴ := by
    simpa only [k,endpointBefore,endpointAfter] using hK r t f g
  rw [sourceBlock_step e t k.val k.isLt,jointGate_as_product]
  change evolve (T*D) (sourceBlock e t k.val f g)=
    routedLift r V hc (Q f)*rawState t (k.val+1)*(routedLift r V hc (Q g))ᴴ
  rw [hprev,hL,hL,hraw]
  exact (release_cross_evolution _ _ _ _ D T U (hN f) (hN g) (rawState t k.val) hρ).symm

theorem kernelAt_every_cut {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∀ k : Cut S, KernelAt e k (activeVisits S k) := by
  apply Fin.induction
  · exact kernelAt_initial e
  · intro k ih
    obtain ⟨⟨v,o⟩,hpos⟩ := S.position.surjective k
    have hb : k.castSucc=endpointBefore S v o := Fin.ext (congrArg Fin.val hpos).symm
    have ha : k.succ=endpointAfter S v o := Fin.ext (by
      change k.val+1=(S.position (v,o)).val+1
      rw [hpos])
    cases o
    · rw [hb] at ih
      rw [ha,active_arrival_update]
      exact kernelAt_arrival e v ih
    · rw [hb,← releaseOthers_insert] at ih
      rw [ha,active_release_update]
      exact kernelAt_release e v ih

theorem schedule_kernel_from_routed {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∃ K : (k : Cut S) → Fin e.f → CutKernel e k,
      ∀ (r : ℕ) (t : Tester S r) (k : Cut S) (f g : Fin e.f),
        sourceBlock e t (k.val+1) f g=kernelLift e k r (K k f)*rawState t (k.val+1)*
          (kernelLift e k r (K k g))ᴴ := by
  choose hc K hK using kernelAt_every_cut e
  refine ⟨fun k f => cutFromRouted e k _ (held_active_image S k) (K k f),?_⟩
  intro r t k f g
  rw [cutFromRouted_lift e k _ (hc k),cutFromRouted_lift e k _ (hc k)]
  exact hK k r t f g

#print axioms KernelAt
#print axioms kernelAt_initial
#print axioms kernelAt_arrival
#print axioms kernelAt_release
#print axioms kernelAt_every_cut
#print axioms schedule_kernel_from_routed
end ScheduleLaw.Blueprint
