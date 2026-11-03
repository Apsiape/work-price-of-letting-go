import BlueprintOwnedRecovery

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

def registerEquiv {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) :
    Restricted I (visitCarriers S V) ≃ Registers S V :=
  (Equiv.piCongrLeft (fun c : {c // c ∈ visitCarriers S V} => Fin (I.dim c.val))
    (carrierVisits S V hc)).symm

theorem registerEquiv_actual {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (p : Payload I) :
    registerEquiv S V hc (restrictPayload I (visitCarriers S V) p)=selectedVisits S V p := by
  rfl

def routedObservable {I : Inventory} {S : Schedule I} (e : Extension S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (H : Mat (Fin e.b × Restricted I (visitCarriers S V))) : Mat (Fin e.b × Registers S V) :=
  H.submatrix (Equiv.prodCongr (Equiv.refl _) (registerEquiv S V hc).symm)
    (Equiv.prodCongr (Equiv.refl _) (registerEquiv S V hc).symm)

theorem routedObservable_lift {I : Inventory} {S : Schedule I} (e : Extension S)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (H : Mat (Fin e.b × Restricted I (visitCarriers S V))) (r : ℕ) :
    routedLift r V hc (routedObservable e V hc H)=ownedObservable e r (visitCarriers S V) H := by
  ext i j
  rw [routedLift_entry]
  simp only [routedObservable,ownedObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    ownershipCoordinates,Equiv.coe_fn_mk,Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map,
    ← registerEquiv_actual S V hc,Equiv.symm_apply_apply,Prod.mk.injEq]
  by_cases hp : restrictPayload I (visitCarriers S V)ᶜ i.2.1=
      restrictPayload I (visitCarriers S V)ᶜ j.2.1 <;>
    by_cases hm : i.2.2=j.2.2 <;> simp [hp,hm]

theorem routedLift_frame {I : Inventory} {S : Schedule I} {a b : Type} (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (K : Matrix (b × Registers S V) (a × Registers S V) ℂ) :
    (routedLift r V hc K).submatrix (routedFrame S b r V hc).symm (routedFrame S a r V hc).symm=
      K ⊗ₖ (1 : Mat (Restricted I (visitCarriers S V)ᶜ × Fin r)) := by
  ext i j
  simp only [routedLift,submatrix_apply,Equiv.apply_symm_apply]

theorem carrierEnergy_routed {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (V : Finset (Fin S.visits)) (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (c : Fin I.count) (hmem : c ∈ visitCarriers S V) (ρ : Mat (Global e r)) :
    carrierEnergy e ρ c=energy (routedObservable e V hc (ownedCarrier I e.b (visitCarriers S V) c hmem))
      (partialRight (ρ.submatrix (routedFrame S (Fin e.b) r V hc).symm
        (routedFrame S (Fin e.b) r V hc).symm)) := by
  rw [carrierEnergy_as_observable,carrier_owned_matrix e r (visitCarriers S V) c hmem,
    ← routedObservable_lift e V hc]
  have h := energy_reindex (routedFrame S (Fin e.b) r V hc).symm
    (routedLift r V hc (routedObservable e V hc (ownedCarrier I e.b (visitCarriers S V) c hmem))) ρ
  rw [routedLift_frame,energy_kron_one] at h
  exact h.symm

theorem routed_sandwich_owned {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (V : Finset (Fin S.visits))
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits)))
    (K : Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    partialRight ((routedLift r V hc K*rawState t n*(routedLift r V hc K)ᴴ).submatrix
      (routedFrame S (Fin e.b) r V hc).symm (routedFrame S (Fin e.b) r V hc).symm)=
      K*routedOwnedRaw S t n V hc*Kᴴ := by
  rw [cross_reindex _ (routedFrame S (Recorder.Stock S) r V hc).symm,
    routedLift_frame,partialRight_rect_sandwich]
  rfl

theorem routed_energy_terminal_readout {I : Inventory} {S : Schedule I} (e : Extension S)
    (k : Cut S) (V : Finset (Fin S.visits)) (hV : V ⊆ activeVisits S k)
    (hc : Set.InjOn S.carrier (V : Set (Fin S.visits))) (c : Fin I.count)
    (hmem : c ∈ visitCarriers S V)
    (K : Fin e.f → Matrix (Fin e.b × Registers S V) (Recorder.Stock S × Registers S V) ℂ) :
    ∃ L : Mat (Recorder.Stock S) →ₗ[ℝ] ℝ, ∀ (r : ℕ) (t : Tester S r),
      L (terminalStock t)=carrierEnergy e
        (∑ f, routedLift r V hc (K f)*rawState t (k.val+1)*(routedLift r V hc (K f))ᴴ) c := by
  let H := routedObservable e V hc (ownedCarrier I e.b (visitCarriers S V) c hmem)
  let B : Mat (Recorder.Stock S × Registers S V) →ₗ[ℝ] ℝ :=
    ∑ f, (energyLinear H).comp ((sandwichLinear (K f)).restrictScalars ℝ)
  let L := (B.comp ((ownedStockRestore S V).restrictScalars ℝ)).comp
    ((terminalStockAtLinear S (k.val+1)).restrictScalars ℝ)
  refine ⟨L,?_⟩
  intro r t
  have hn : k.val+1 ≤ 2*S.visits+1 := by have := k.isLt; omega
  change B (ownedStockRestore S V (terminalStockAtLinear S (k.val+1) (terminalStock t)))=_
  rw [terminalStockAtLinear_actual S t _ hn,ownedStockRestore_actual S t k V hV]
  have hsum : carrierEnergy e
      (∑ f, routedLift r V hc (K f)*rawState t (k.val+1)*(routedLift r V hc (K f))ᴴ) c=
      ∑ f, carrierEnergy e (routedLift r V hc (K f)*rawState t (k.val+1)*(routedLift r V hc (K f))ᴴ) c := by
    simp only [carrierEnergy_as_observable]
    exact map_sum (energyLinear _) _ _
  rw [hsum]
  simp only [B,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.restrictScalars_apply,
    sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro f _
  rw [carrierEnergy_routed e r V hc c hmem,routed_sandwich_owned]
  rfl

#print axioms registerEquiv
#print axioms registerEquiv_actual
#print axioms routedObservable
#print axioms routedObservable_lift
#print axioms routedLift_frame
#print axioms carrierEnergy_routed
#print axioms routed_sandwich_owned
#print axioms routed_energy_terminal_readout
end ScheduleLaw.Blueprint
