import ScheduleEnergy

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw

theorem conserves_reindex {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (U H : Mat b)
    (h : Conserves U H) : Conserves (U.submatrix e e) (H.submatrix e e) := by
  unfold Conserves at *
  rw [conjTranspose_submatrix,submatrix_mul_equiv,submatrix_mul_equiv,h]

theorem conserves_kron {a b : Type} [Fintype a] [Fintype b]
    (U H : Mat a) (V K : Mat b) (hU : Conserves U H) (hV : Conserves V K) :
    Conserves (U ⊗ₖ V) (H ⊗ₖ K) := by
  unfold Conserves at *
  rw [conjTranspose_kronecker,← mul_kronecker_mul,← mul_kronecker_mul,hU,hV]

theorem evolve_mul {a : Type} [Fintype a] (U V ρ : Mat a) :
    evolve (U*V) ρ = evolve U (evolve V ρ) := by
  simp only [evolve,conjTranspose_mul,mul_assoc]

theorem energy_add {a : Type} [Fintype a] (H K ρ : Mat a) :
    energy (H+K) ρ = energy H ρ + energy K ρ := by
  simp [energy,add_mul,trace_add]

theorem energy_sum {a b : Type} [Fintype a] [Fintype b]
    (H : b → Mat a) (ρ : Mat a) : energy (∑ i,H i) ρ = ∑ i,energy (H i) ρ := by
  simp [energy,Finset.sum_mul,trace_sum]

theorem energy_reindex {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (H ρ : Mat b) :
    energy (H.submatrix e e) (ρ.submatrix e e) = energy H ρ := by
  unfold energy
  rw [submatrix_mul_equiv,submatrix_trace_equiv]

theorem energy_kron_one {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (H : Mat a) (ρ : Mat (a × b)) :
    energy (H ⊗ₖ (1 : Mat b)) ρ = energy H (partialRight ρ) := by
  unfold energy
  congr 1
  simp only [trace,diag_apply,mul_apply,Fintype.sum_prod_type,kroneckerMap_apply,
    one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.sum_ite_eq,
    Finset.mem_univ,if_true,partialRight,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem energy_one_kron {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (H : Mat b) (ρ : Mat (a × b)) :
    energy ((1 : Mat a) ⊗ₖ H) ρ = energy H (partialLeft ρ) := by
  rw [← energy_reindex (Equiv.prodComm b a),kron_swap,energy_kron_one]
  rfl

def Engine.bodyHamiltonian {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) : Mat (Fin e.extension.b) :=
  (e.HC.matrix ⊗ₖ (1 : Mat (Fin e.w × Fin e.r)) +
    (1 : Mat (Fin e.c)) ⊗ₖ
      ((diagonal fun j => (e.batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin e.r)) +
        (1 : Mat (Fin e.w)) ⊗ₖ e.HR.matrix)).submatrix e.split e.split

def liftDeviceObservable {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (H : Mat (Fin e.b × Payload I)) : Mat (Global e r) :=
  (H ⊗ₖ (1 : Mat (Fin r))).submatrix
    (Equiv.prodAssoc (Fin e.b) (Payload I) (Fin r)).symm
    (Equiv.prodAssoc (Fin e.b) (Payload I) (Fin r)).symm

def liftTesterObservable {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (H : Mat (Fin r × Payload I)) : Mat (Global e r) :=
  (1 : Mat (Fin e.b)) ⊗ₖ
    (H.submatrix (Equiv.prodComm (Payload I) (Fin r))
      (Equiv.prodComm (Payload I) (Fin r)))

theorem lifted_carrier_agrees {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (c : Fin I.count) :
    liftDeviceObservable e r (carrierObservable I e.b c) =
      liftTesterObservable e r (carrierObservable I r c) := by
  ext i j
  simp only [liftDeviceObservable,liftTesterObservable,submatrix_apply,kroneckerMap_apply,
    one_apply,carrierObservable,Equiv.prodAssoc_symm_apply,Equiv.prodComm_apply]
  by_cases hb : i.1 = j.1 <;> by_cases hr : i.2.2 = j.2.2 <;>
    by_cases hc : ∀ d, d ≠ c → i.2.1 d = j.2.1 d <;> simp [hb,hr,hc]

theorem carrierEnergy_as_observable {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (ρ : Mat (Global e r)) (c : Fin I.count) :
    carrierEnergy e ρ c = energy (liftDeviceObservable e r (carrierObservable I e.b c)) ρ := by
  unfold carrierEnergy
  apply congrArg (fun H : Mat (Global e r) => energy H ρ)
  ext i j
  simp only [liftDeviceObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    carrierObservable,Equiv.prodAssoc_symm_apply]
  by_cases hb : i.1 = j.1 <;> by_cases hr : i.2.2 = j.2.2 <;>
    by_cases hc : ∀ d, d ≠ c → i.2.1 d = j.2.1 d <;> simp [hb,hr,hc]

theorem conserves_one {a : Type} [Fintype a] [DecidableEq a]
    (U : Mat a) (hU : IsUnitary U) : Conserves U 1 := by
  simpa [Conserves] using hU.1

theorem liftDevice_conserves {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (U H : Mat (Fin e.b × Payload I))
    (h : Conserves U H) :
    Conserves (liftDeviceObservable e r U) (liftDeviceObservable e r H) := by
  exact conserves_reindex _ _ _ (conserves_kron U H 1 1 h (by simp [Conserves]))

theorem liftTester_conserves {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (U H : Mat (Fin r × Payload I))
    (h : Conserves U H) :
    Conserves (liftTesterObservable e r U) (liftTesterObservable e r H) := by
  exact conserves_kron 1 1 _ _ (by simp [Conserves]) (conserves_reindex _ _ _ h)

theorem liftDevice_body {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (H : Mat (Fin e.b)) :
    liftDeviceObservable e r (H ⊗ₖ (1 : Mat (Payload I))) =
      H ⊗ₖ (1 : Mat (Payload I × Fin r)) := by
  ext i j
  simp only [liftDeviceObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    Equiv.prodAssoc_symm_apply,Prod.mk.injEq]
  by_cases hp : i.2.1 = j.2.1 <;> by_cases hr : i.2.2 = j.2.2 <;> simp [Prod.ext_iff,hp,hr]

theorem tester_conserves_body {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (k : Cut S) (H : Mat (Fin e.b)) :
    Conserves (liftTesterObservable e r (t.gate k))
      (liftDeviceObservable e r (H ⊗ₖ (1 : Mat (Payload I)))) := by
  rw [liftDevice_body]
  exact conserves_kron 1 H _ 1 (by simp [Conserves])
    (conserves_one _ (unitary_submatrix _ (t.unitary k)))

theorem payloadHamiltonian_as_sum (I : Inventory) (b : ℕ) :
    (1 : Mat (Fin b)) ⊗ₖ payloadHamiltonian I = ∑ c,carrierObservable I b c := by
  ext i j
  simp only [payloadHamiltonian,kroneckerMap_apply,carrierObservable,one_apply,
    Matrix.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hb : i.1 = j.1 <;> by_cases hc : ∀ d, d ≠ c → i.2 d = j.2 d <;>
    simp [hb,hc]

theorem liftDevice_add {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (H K : Mat (Fin e.b × Payload I)) :
    liftDeviceObservable e r (H+K) = liftDeviceObservable e r H + liftDeviceObservable e r K := by
  ext i j
  simp [liftDeviceObservable,kroneckerMap_apply,add_mul]

theorem liftDevice_sum {I : Inventory} {S : Schedule I} {a : Type} [Fintype a]
    (e : Extension S) (r : ℕ) (H : a → Mat (Fin e.b × Payload I)) :
    liftDeviceObservable e r (∑ i,H i) = ∑ i,liftDeviceObservable e r (H i) := by
  ext i j
  simp [liftDeviceObservable,kroneckerMap_apply,Finset.sum_mul,Matrix.sum_apply]

theorem jointGate_as_product {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (k : Cut S) :
    jointGate e t k = liftTesterObservable e r (t.gate k) *
      liftDeviceObservable e r (e.gate k) := rfl

theorem cut_energy_balance {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) (k : Cut S)
    (ρ : Mat (Global e.extension r)) :
    energy (e.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I × Fin r)))
        (evolve (jointGate e.extension t k) ρ) -
      energy (e.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I × Fin r))) ρ +
      (∑ c ∈ held S k, (carrierEnergy e.extension (evolve (jointGate e.extension t k) ρ) c -
        carrierEnergy e.extension ρ c)) = 0 := by
  let Ud := liftDeviceObservable e.extension r (e.extension.gate k)
  let Ut := liftTesterObservable e.extension r (t.gate k)
  let ρd := evolve Ud ρ
  let ρf := evolve (jointGate e.extension t k) ρ
  let HB := e.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I × Fin r))
  have hf : ρf = evolve Ut ρd := by
    dsimp [ρf,ρd,Ut,Ud]
    rw [jointGate_as_product,evolve_mul]
  have hd := energy_conserved Ud
    (liftDeviceObservable e.extension r
      (e.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I)) +
        (1 : Mat (Fin e.extension.b)) ⊗ₖ payloadHamiltonian I)) ρ
    (liftDevice_conserves e.extension r _ _ (e.gate_conserves k))
  simp only [payloadHamiltonian_as_sum,liftDevice_add,liftDevice_sum,energy_add,energy_sum,
    liftDevice_body] at hd
  simp_rw [← carrierEnergy_as_observable] at hd
  change energy HB ρd + (∑ c,carrierEnergy e.extension ρd c) =
    energy HB ρ + ∑ c,carrierEnergy e.extension ρ c at hd
  have hb : energy HB ρf = energy HB ρd := by
    rw [hf]
    exact energy_conserved Ut HB ρd (by
      simpa only [liftDevice_body] using tester_conserves_body e.extension t k e.bodyHamiltonian)
  have hinactive : ∀ c, c ∉ held S k →
      carrierEnergy e.extension ρd c = carrierEnergy e.extension ρ c := by
    intro c hc
    rw [carrierEnergy_as_observable,carrierEnergy_as_observable]
    exact energy_conserved Ud _ ρ (liftDevice_conserves e.extension r _ _
      (local_conserves_unheld_carrier I e.extension.b (held S k)
        (e.extension.gate k) (e.extension.gate_local k) c hc))
  have hactive : ∀ c ∈ held S k,
      carrierEnergy e.extension ρf c = carrierEnergy e.extension ρd c := by
    intro c hc
    rw [hf,carrierEnergy_as_observable,carrierEnergy_as_observable,lifted_carrier_agrees]
    exact energy_conserved Ut _ ρd (liftTester_conserves e.extension r _ _
      (local_conserves_unheld_carrier I r (held S k)ᶜ (t.gate k)
        (t.gate_local k) c (by simpa using hc)))
  have hs : (∑ c ∈ held S k,(carrierEnergy e.extension ρf c - carrierEnergy e.extension ρ c)) =
      ∑ c,(carrierEnergy e.extension ρd c - carrierEnergy e.extension ρ c) := by
    calc
      _ = ∑ c ∈ held S k,(carrierEnergy e.extension ρd c - carrierEnergy e.extension ρ c) :=
        Finset.sum_congr rfl (fun c hc => by rw [hactive c hc])
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => by
        rw [hinactive c hc,sub_self])
  change energy HB ρf - energy HB ρ +
    (∑ c ∈ held S k,(carrierEnergy e.extension ρf c - carrierEnergy e.extension ρ c)) = 0
  rw [hb,hs,Finset.sum_sub_distrib]
  linarith

theorem partialRight_kron {a b : Type} [Fintype a] [Fintype b]
    (A : Mat a) (B : Mat b) : partialRight (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp [partialRight,kroneckerMap_apply,trace,← Finset.mul_sum,smul_eq_mul,mul_comm]

theorem initial_body_reduction {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    partialRight (initialState e t) = e.source.matrix := by
  have ht := (initialState_density e t).2
  rw [initialState,trace_kronecker,e.source.normalized,one_mul] at ht
  rw [initialState,partialRight_kron,ht,one_smul]

theorem body_handoff_energy_balance {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :
    energy e.bodyHamiltonian (bodyOutput e.extension t) -
      energy e.bodyHamiltonian e.extension.source.matrix + handoff e.extension t = 0 := by
  let f : ℕ → ℝ := fun n =>
    energy (e.bodyHamiltonian ⊗ₖ (1 : Mat (Payload I × Fin r))) (run e.extension t n)
  let g : Fin I.count → ℕ → ℝ := fun c n => carrierEnergy e.extension (run e.extension t n) c
  have hstep : ∀ k : Cut S,f (k.val+1)-f k.val +
      (∑ c ∈ held S k,(g c (k.val+1)-g c k.val)) = 0 := by
    intro k
    dsimp [f,g]
    rw [run,dif_pos k.isLt]
    exact cut_energy_balance e t k (run e.extension t k.val)
  have h := schedule_energy_telescope S f g hstep
  dsimp [f,g] at h
  rw [energy_kron_one,energy_kron_one,run,initial_body_reduction] at h
  exact h

theorem partialLeft_kron {a b : Type} [Fintype a] [Fintype b]
    (A : Mat a) (B : Mat b) : partialLeft (A ⊗ₖ B) = A.trace • B := by
  ext i j
  simp [partialLeft,kroneckerMap_apply,trace,← Finset.sum_mul,smul_eq_mul]

theorem battery_diagonal_energy {a : Type} [Fintype a] [DecidableEq a]
    (E : a → ℝ) (ρ : Mat a) :
    energy (diagonal (fun i => (E i : ℂ))) ρ = ∑ i,E i * (ρ i i).re := by
  simp [energy,trace,mul_apply,diagonal_apply,ite_mul,Complex.mul_re]

theorem bodyEnergy_decomposition {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (ρ : Mat (Fin e.extension.b)) :
    energy e.bodyHamiltonian ρ =
      energy e.HC.matrix (partialRight (ρ.submatrix e.split.symm e.split.symm)) +
        energy (diagonal fun j => (e.batteryEnergy j : ℂ))
          (partialRight (partialLeft (ρ.submatrix e.split.symm e.split.symm))) +
        energy e.HR.matrix (partialLeft (partialLeft (ρ.submatrix e.split.symm e.split.symm))) := by
  rw [← energy_reindex e.split.symm e.bodyHamiltonian ρ]
  have hh : e.bodyHamiltonian.submatrix e.split.symm e.split.symm =
      e.HC.matrix ⊗ₖ (1 : Mat (Fin e.w × Fin e.r)) +
        (1 : Mat (Fin e.c)) ⊗ₖ
          ((diagonal fun j => (e.batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin e.r)) +
            (1 : Mat (Fin e.w)) ⊗ₖ e.HR.matrix) := by
    ext i j
    simp [Engine.bodyHamiltonian,submatrix_apply]
  rw [hh,energy_add,energy_kron_one,energy_one_kron,energy_add,
    energy_kron_one,energy_one_kron]
  ring

theorem bodyEnergy_final {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :
    energy e.bodyHamiltonian (bodyOutput e.extension t) =
      energy e.HC.matrix (controllerFinal e t) + batteryMeanFinal e t +
        energy e.HR.matrix (reservoirFinal e t) := by
  rw [bodyEnergy_decomposition,battery_diagonal_energy]
  rfl

theorem bodyEnergy_initial {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) : energy e.bodyHamiltonian e.extension.source.matrix =
      energy e.HC.matrix e.controller.matrix + e.batteryEnergy e.initialLevel +
        energy e.HR.matrix (gibbs β e.HR) := by
  letI : Nonempty (Fin e.r) := ⟨⟨0,e.r_pos⟩⟩
  let P : Mat (Fin e.w) := pureMatrix (fun i => if i = e.initialLevel then 1 else 0)
  have hP : P.trace = 1 := by
    dsimp [P]
    rw [pureMatrix_trace]
    simp
  have hp : e.extension.source.matrix.submatrix e.split.symm e.split.symm =
      e.controller.matrix ⊗ₖ (P ⊗ₖ gibbs β e.HR) := by
    rw [e.source_product]
    ext i j
    simp [submatrix_apply,P]
  rw [bodyEnergy_decomposition,hp]
  simp only [partialRight_kron,partialLeft_kron,trace_kronecker,hP,gibbs_trace,
    e.controller.normalized,mul_one,one_smul]
  have hPE : energy (diagonal fun j => (e.batteryEnergy j : ℂ)) P =
      e.batteryEnergy e.initialLevel := by
    rw [battery_diagonal_energy]
    simp [P,pureMatrix,mul_ite,ite_mul,apply_ite]
  rw [hPE]

theorem energy_accounting_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) :
    (engineLedger e t).controllerEnergy + (engineLedger e t).batteryEnergy +
      (engineLedger e t).reservoirEnergy + (engineLedger e t).handoffEnergy = 0 := by
  have h := body_handoff_energy_balance e t
  rw [bodyEnergy_final,bodyEnergy_initial] at h
  dsimp [engineLedger,controllerEnergyChange,batteryEnergyChange]
  linarith

end ScheduleLaw
