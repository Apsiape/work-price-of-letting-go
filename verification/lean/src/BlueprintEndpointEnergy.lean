import BlueprintEnergyReadout

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

theorem tester_held_energy_invariant {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (c : Fin I.count) (hc : c ∈ held S k)
    (ρ : Mat (Global e r)) :
    carrierEnergy e (evolve (liftTesterObservable e r (t.gate k)) ρ) c=carrierEnergy e ρ c := by
  rw [carrierEnergy_owned e r (held S k) c hc,carrierEnergy_owned e r (held S k) c hc,
    owned_tester_invariant]

theorem arrival_probe_family {I : Inventory} {S : Schedule I} (e : Extension S) (v : Fin S.visits) :
    let V := activeVisits S (endpointBefore S v false)
    ∃ (hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)))
      (P : Fin e.f → Matrix (Fin e.b × Registers S (insert v V))
        (Recorder.Stock S × Registers S (insert v V)) ℂ),
      ∀ (r : ℕ) (t : Tester S r),
        (∑ f, routedLift r (insert v V) hc (P f)*rawState t ((endpointAfter S v false).val+1)*
          (routedLift r (insert v V) hc (P f))ᴴ)=
        evolve (liftTesterObservable e r (t.gate (endpointAfter S v false)))
          (run e t ((endpointBefore S v false).val+1)) := by
  let V := activeVisits S (endpointBefore S v false)
  have hv : v ∉ V := by simp [V,activeVisits,endpointBefore]
  have hc : Set.InjOn S.carrier ((insert v V : Finset (Fin S.visits)) : Set (Fin S.visits)) := by
    rw [← active_arrival_update]
    exact activeVisits_carriers_injective S _ _ (Finset.Subset.refl _)
  have hA : held S (endpointAfter S v false)=visitCarriers S (insert v V) := by
    rw [held_active_image,active_arrival_update]
  obtain ⟨hcP,K,hK⟩ := kernelAt_every_cut e (endpointBefore S v false)
  let k := endpointAfter S v false
  let P := fun f => routedArrival V v hv (K f)
  refine ⟨hc,P,?_⟩
  intro r t
  let T := liftTesterObservable e r (t.gate k)
  let U := testerOperator t k
  have hC (f : Fin e.f) : routedLift r (insert v V) hc (P f)*(wire k r).permMatrix ℂ=
      routedLift r V hcP (K f) := routedArrival_cancellation r V v hv hc (K f)
  have hN (f : Fin e.f) : ((1 : Mat (Global e r))*routedLift r (insert v V) hc (P f))*U=
      T*((1 : Mat (Global e r))*routedLift r (insert v V) hc (P f)) := by
    simpa only [Matrix.one_mul,T,U] using routed_kernel_tester e t k _ hc hA (P f)
  have hcross (f : Fin e.f) :
      routedLift r (insert v V) hc (P f)*rawState t (k.val+1)*
        (routedLift r (insert v V) hc (P f))ᴴ=
      evolve T (sourceBlock e t ((endpointBefore S v false).val+1) f f) := by
    have hprev : sourceBlock e t ((endpointBefore S v false).val+1) f f=
        routedLift r V hcP (K f)*rawState t k.val*(routedLift r V hcP (K f))ᴴ := by
      simpa only [k,endpointBefore,endpointAfter] using hK r t f f
    rw [hprev,rawState_step S t k.val k.isLt]
    simpa only [Matrix.one_mul,Matrix.mul_one,T,U] using
      arrival_cross_evolution _ _ _ _ (1 : Mat (Global e r)) T U ((wire k r).permMatrix ℂ)
        (hC f) (hC f) (hN f) (hN f) (rawState t k.val)
  rw [sourceBlock_sum e t ((endpointBefore S v false).val+1)]
  change _=(sandwichLinear T) (∑ f, sourceBlock e t ((endpointBefore S v false).val+1) f f)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun f _ => hcross f)

theorem arrival_energy_readout {I : Inventory} {S : Schedule I} (e : Extension S) (v : Fin S.visits) :
    ∃ L : Mat (Recorder.Stock S) →ₗ[ℝ] ℝ, ∀ (r : ℕ) (t : Tester S r),
      L (terminalStock t)=carrierEnergy e (run e t ((S.position (v,false)).val+1)) (S.carrier v) := by
  let V := activeVisits S (endpointBefore S v false)
  obtain ⟨hc,P,hP⟩ := arrival_probe_family e v
  have hV : insert v V ⊆ activeVisits S (endpointAfter S v false) := by
    rw [active_arrival_update]
  have hmem : S.carrier v ∈ visitCarriers S (insert v V) :=
    Finset.mem_image.mpr ⟨v,Finset.mem_insert_self _ _,rfl⟩
  obtain ⟨L,hL⟩ := routed_energy_terminal_readout e (endpointAfter S v false)
    (insert v V) hV hc (S.carrier v) hmem P
  refine ⟨L,?_⟩
  intro r t
  rw [hL r t,hP r t]
  exact tester_held_energy_invariant e t (endpointAfter S v false) (S.carrier v)
    (Recorder.carrier_held_at_arrival v) _

theorem release_energy_readout {I : Inventory} {S : Schedule I} (e : Extension S) (v : Fin S.visits) :
    ∃ L : Mat (Recorder.Stock S) →ₗ[ℝ] ℝ, ∀ (r : ℕ) (t : Tester S r),
      L (terminalStock t)=carrierEnergy e (run e t ((S.position (v,true)).val+1)) (S.carrier v) := by
  let k := endpointBefore S v true
  let V := activeVisits S k
  obtain ⟨hc,K,hK⟩ := kernelAt_every_cut e k
  have hmem : S.carrier v ∈ visitCarriers S V :=
    Finset.mem_image.mpr ⟨v,visit_active_before_release S v,rfl⟩
  obtain ⟨L,hL⟩ := routed_energy_terminal_readout e k V (Finset.Subset.refl _) hc (S.carrier v) hmem K
  refine ⟨L,?_⟩
  intro r t
  rw [hL r t]
  change carrierEnergy e (∑ f, routedLift r V hc (K f)*rawState t (k.val+1)*
      (routedLift r V hc (K f))ᴴ) (S.carrier v)=carrierEnergy e (run e t (k.val+1)) (S.carrier v)
  rw [sourceBlock_sum e t (k.val+1)]
  congr 1
  exact Finset.sum_congr rfl (fun f _ => (hK r t f f).symm)

theorem endpoint_energy_from_routed {I : Inventory} {S : Schedule I} (e : Extension S)
    (v : Fin S.visits) (o : Bool) :
    ∃ L : Mat (Recorder.Stock S) →ₗ[ℝ] ℝ, ∀ (r : ℕ) (t : Tester S r),
      L (terminalStock t)=carrierEnergy e (run e t ((S.position (v,o)).val+1)) (S.carrier v) := by
  cases o
  · exact arrival_energy_readout e v
  · exact release_energy_readout e v

#print axioms tester_held_energy_invariant
#print axioms arrival_probe_family
#print axioms arrival_energy_readout
#print axioms release_energy_readout
#print axioms endpoint_energy_from_routed
end ScheduleLaw.Blueprint
