import OwnedReadout
import FlagAccounting

/-! The actual signed handoff is a linear readout of the complete owned
cut history. This uses schedule telescoping and the actual local gates;
it does not assert that the owned history factors through the wire Gram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

def energyLinear {a : Type} [Fintype a] (H : Mat a) : Mat a →ₗ[ℝ] ℝ where
  toFun := energy H
  map_add' A B := ClassicalFlag.energy_state_add H A B
  map_smul' c A := ClassicalFlag.energy_weight H A c

theorem energy_pullback {a : Type} [Fintype a] (H U ρ : Mat a) :
    energy H (evolve U ρ) = energy (Uᴴ * H * U) ρ := by
  unfold energy evolve
  rw [← mul_assoc H (U*ρ) Uᴴ,trace_mul_comm (H*(U*ρ)) Uᴴ]
  simp only [mul_assoc]

theorem energy_sub_observable {a : Type} [Fintype a] (H K ρ : Mat a) :
    energy (H-K) ρ = energy H ρ - energy K ρ := by simp [energy,sub_mul,trace_sub]

def ownedObservable {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (H : Mat (Fin e.b × Restricted I A)) : Mat (Global e r) :=
  (H ⊗ₖ (1 : Mat (Fin r × Restricted I Aᶜ))).submatrix
    (ownershipCoordinates e r A) (ownershipCoordinates e r A)

theorem energy_owned_observable {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (H : Mat (Fin e.b × Restricted I A))
    (ρ : Mat (Global e r)) : energy (ownedObservable e r A H) ρ =
      energy H (ownedMarginal e r A ρ) := by
  have he := energy_reindex (ownershipCoordinates e r A).symm (ownedObservable e r A H) ρ
  have hm : (ownedObservable e r A H).submatrix (ownershipCoordinates e r A).symm
      (ownershipCoordinates e r A).symm = H ⊗ₖ (1 : Mat (Fin r × Restricted I Aᶜ)) := by
    ext i j
    simp only [ownedObservable,submatrix_apply,Equiv.apply_symm_apply]
  rw [hm,energy_kron_one] at he
  exact he.symm

def ownedCarrier (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (c : Fin I.count) (hc : c ∈ A) : Mat (Fin b × Restricted I A) := fun i j =>
  (if i.1 = j.1 ∧ (∀ d : {d // d ∈ A}, d.val ≠ c → i.2 d = j.2 d) then 1 else 0) *
    (I.H c).matrix (i.2 ⟨c,hc⟩) (j.2 ⟨c,hc⟩)

theorem other_coordinates_owned (I : Inventory) (A : Finset (Fin I.count))
    (c : Fin I.count) (hc : c ∈ A) (p q : Payload I) :
    (∀ d, d ≠ c → p d = q d) ↔
      (∀ d : {d // d ∈ A}, d.val ≠ c → p d.val = q d.val) ∧
        restrictPayload I Aᶜ p = restrictPayload I Aᶜ q := by
  constructor
  · intro he
    refine ⟨fun d hd => he d.val hd,?_⟩
    funext d
    exact he d.val (fun hd => (Finset.mem_compl.mp d.property) (hd ▸ hc))
  · rintro ⟨hA,hR⟩ d hd
    by_cases hm : d ∈ A
    · exact hA ⟨d,hm⟩ hd
    · exact congrFun hR ⟨d,Finset.mem_compl.mpr hm⟩

theorem carrier_owned_matrix {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (c : Fin I.count) (hc : c ∈ A) :
    liftDeviceObservable e r (carrierObservable I e.b c) =
      ownedObservable e r A (ownedCarrier I e.b A c hc) := by
  apply device_owned_matrix
  intro i j
  have hh := other_coordinates_owned I A c hc i.2 j.2
  change (if i.1 = j.1 ∧ (∀ d, d ≠ c → i.2 d = j.2 d) then 1 else 0) *
    (I.H c).matrix (i.2 c) (j.2 c) =
      (if i.1 = j.1 ∧ (∀ d : {d // d ∈ A}, d.val ≠ c → i.2 d.val = j.2 d.val) then 1 else 0) *
        (I.H c).matrix (i.2 c) (j.2 c) *
          if restrictPayload I Aᶜ i.2 = restrictPayload I Aᶜ j.2 then 1 else 0
  simp only [hh]
  by_cases hb : i.1 = j.1 <;>
    by_cases ho : ∀ d : {d // d ∈ A}, d.val ≠ c → i.2 d.val = j.2 d.val <;>
    by_cases hr : restrictPayload I Aᶜ i.2 = restrictPayload I Aᶜ j.2 <;>
    simp [hb,ho,hr]

theorem carrierEnergy_owned {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (c : Fin I.count) (hc : c ∈ A) (ρ : Mat (Global e r)) :
    carrierEnergy e ρ c = energy (ownedCarrier I e.b A c hc) (ownedMarginal e r A ρ) := by
  rw [carrierEnergy_as_observable,carrier_owned_matrix e r A c hc,energy_owned_observable]

def contactEnergyObservable {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S)
    (c : Fin I.count) (hc : c ∈ held S k) : Mat (Fin e.b × Restricted I (held S k)) :=
  (localContactGate e k)ᴴ * ownedCarrier I e.b (held S k) c hc * localContactGate e k -
    ownedCarrier I e.b (held S k) c hc

theorem actual_cut_carrier_change {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (c : Fin I.count) (hc : c ∈ held S k)
    (ρ : Mat (Global e r)) :
    carrierEnergy e (evolve (jointGate e t k) ρ) c - carrierEnergy e ρ c =
      energy (contactEnergyObservable e k c hc) (ownedMarginal e r (held S k) ρ) := by
  rw [carrierEnergy_owned e r (held S k) c hc,
    carrierEnergy_owned e r (held S k) c hc,owned_joint_contact,energy_pullback]
  exact (energy_sub_observable _ _ _).symm

def contactEnergyReadout {I : Inventory} {S : Schedule I} (e : Extension S) (k : Cut S) :
    Mat (Fin e.b × Restricted I (held S k)) →ₗ[ℝ] ℝ :=
  ∑ c : Fin I.count, if hc : c ∈ held S k then energyLinear (contactEnergyObservable e k c hc) else 0

theorem contactEnergyReadout_actual {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) :
    contactEnergyReadout e k (ownedHistory e t k) =
      ∑ c ∈ held S k, (carrierEnergy e (run e t (k.val+1)) c - carrierEnergy e (run e t k.val) c) := by
  have hs (f : Fin I.count → ℝ) : (∑ c ∈ held S k, f c) =
      ∑ c : Fin I.count, if c ∈ held S k then f c else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hs]
  unfold contactEnergyReadout
  rw [LinearMap.sum_apply]
  change (∑ c, (if hc : c ∈ held S k then energyLinear (contactEnergyObservable e k c hc) else 0)
    (ownedHistory e t k)) = _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c ∈ held S k
  · rw [dif_pos hc,if_pos hc]
    change energy (contactEnergyObservable e k c hc) (ownedMarginal e r (held S k) _) = _
    rw [← actual_cut_carrier_change e t k c hc,run,dif_pos k.isLt]
  · simp only [dif_neg hc,if_neg hc,LinearMap.zero_apply]

theorem handoff_owned_readout {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) :
    handoff e t = ∑ k : Cut S, contactEnergyReadout e k (ownedHistory e t k) := by
  simp_rw [contactEnergyReadout_actual]
  let g := fun c n => carrierEnergy e (run e t n) c
  have he : (∑ k : Cut S,∑ c ∈ held S k, (g c (k.val+1)-g c k.val)) = handoff e t := by
    calc (∑ k : Cut S,∑ c ∈ held S k, (g c (k.val+1)-g c k.val))
        = ∑ k : Cut S,∑ v ∈ Finset.univ.filter (fun v : Fin S.visits =>
          (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val),
            (g (S.carrier v) (k.val+1)-g (S.carrier v) k.val) := by
          apply Finset.sum_congr rfl
          intro k _
          exact (sum_active_visits S k _).symm
      _ = ∑ v : Fin S.visits, ∑ k : Cut S,
          if (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val
          then g (S.carrier v) (k.val+1)-g (S.carrier v) k.val else 0 := by
          simp only [Finset.sum_filter]
          exact Finset.sum_comm
      _ = handoff e t := Finset.sum_congr rfl (fun v _ => visit_telescope_fin S v (g (S.carrier v)))
  exact he.symm

end ScheduleLaw.History
