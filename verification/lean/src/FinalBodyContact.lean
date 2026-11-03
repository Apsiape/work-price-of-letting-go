import BlueprintTesterCut
import EmptyContact

/-! A square unitary appended to the last body contact. Its action is on the
actual extension, including its complete coherent-tester history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def finalCut {I : Inventory} (S : Schedule I) : Cut S := ⟨2*S.visits,by omega⟩

theorem body_tensor_local (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Fin b)) (hU : IsUnitary U) : LocalOn I b A (U ⊗ₖ 1) := by
  refine ⟨U ⊗ₖ 1,unitary_kron hU (by constructor <;> simp),?_⟩
  intro i j
  have he : i.2=j.2 ↔ restrictPayload I A i.2=restrictPayload I A j.2 ∧
      restrictPayload I Aᶜ i.2=restrictPayload I Aᶜ j.2 := by
    rw [restriction_eq_iff,restriction_eq_iff]
    constructor
    · intro h; rw [h]; simp
    · rintro ⟨ha,hb⟩; funext c
      by_cases hc : c ∈ A
      · exact ha c hc
      · exact hb c (Finset.mem_compl.mpr hc)
  simp only [kroneckerMap_apply,one_apply,he]
  split_ifs <;> simp_all

def finalBodyContact {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) : Extension S where
  b := e.b
  b_pos := e.b_pos
  source := e.source
  f := e.f
  f_pos := e.f_pos
  purification := e.purification
  purification_norm := e.purification_norm
  purification_reduces := e.purification_reduces
  gate k := if k=finalCut S then (U ⊗ₖ 1)*e.gate k else e.gate k
  unitary k := by
    split_ifs
    · exact unitary_mul (unitary_kron hU (by constructor <;> simp)) (e.unitary k)
    · exact e.unitary k
  gate_local k := by
    split_ifs
    · exact localOn_mul I e.b _ _ _ (body_tensor_local I e.b _ U hU) (e.gate_local k)
    · exact e.gate_local k

theorem finalBodyContact_initial {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    initialState (finalBodyContact e U hU) t = initialState e t := rfl

theorem finalBodyContact_joint_before {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r)
    (k : Cut S) (hk : k ≠ finalCut S) :
    jointGate (finalBodyContact e U hU) t k = jointGate e t k := by
  simp only [jointGate,finalBodyContact,if_neg hk]

theorem finalBodyContact_run_before {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r)
    (n : ℕ) (hn : n ≤ 2*S.visits) :
    run (finalBodyContact e U hU) t n = run e t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,run]
    split_ifs with h
    · rw [ih (by omega),finalBodyContact_joint_before e U hU t _ (by
        intro he; have hv := congrArg Fin.val he; dsimp [finalCut] at hv; omega)]
    · exact ih (by omega)

theorem finalBodyContact_joint_last {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    jointGate (finalBodyContact e U hU) t (finalCut S) =
      (U ⊗ₖ (1 : Mat (Payload I × Fin r))) * jointGate e t (finalCut S) := by
  have hg : (finalBodyContact e U hU).gate (finalCut S) =
      (U ⊗ₖ 1)*e.gate (finalCut S) := if_pos rfl
  rw [jointGate_as_product,jointGate_as_product]
  change liftTesterObservable e r (t.gate (finalCut S)) *
    liftDeviceObservable e r ((finalBodyContact e U hU).gate (finalCut S)) = _
  rw [hg]
  have hm (A B : Mat (Fin e.b × Payload I)) :
      liftDeviceObservable e r (A*B) = liftDeviceObservable e r A * liftDeviceObservable e r B := by
    unfold liftDeviceObservable
    rw [submatrix_mul_equiv,← mul_kronecker_mul,one_mul]
  rw [hm,liftDevice_body]
  have hc : liftTesterObservable e r (t.gate (finalCut S)) * (U ⊗ₖ 1) =
      (U ⊗ₖ 1) * liftTesterObservable e r (t.gate (finalCut S)) := by
    unfold liftTesterObservable
    rw [← mul_kronecker_mul,← mul_kronecker_mul,one_mul,mul_one,one_mul,mul_one]
  rw [← mul_assoc,hc,mul_assoc]

theorem finalBodyContact_finalState {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    finalState (finalBodyContact e U hU) t =
      evolve (U ⊗ₖ (1 : Mat (Payload I × Fin r))) (finalState e t) := by
  unfold finalState
  rw [run,run,dif_pos (by omega),dif_pos (by omega),
    finalBodyContact_run_before e U hU t _ le_rfl]
  change evolve (jointGate (finalBodyContact e U hU) t (finalCut S)) _ =
    evolve _ (evolve (jointGate e t (finalCut S)) _)
  rw [finalBodyContact_joint_last,evolve_mul]

theorem finalBodyContact_bodyOutput {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    bodyOutput (finalBodyContact e U hU) t = evolve U (bodyOutput e t) := by
  unfold bodyOutput
  rw [finalBodyContact_finalState,partialRight_evolve_kron_one]

theorem finalBodyContact_observerOutput {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    observerOutput (finalBodyContact e U hU) t = observerOutput e t := by
  unfold observerOutput
  rw [finalBodyContact_finalState,partialLeft_evolve_kron_one _ _ hU]

theorem finalBodyContact_handoff {I : Inventory} {S : Schedule I} (e : Extension S)
    (U : Mat (Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    handoff (finalBodyContact e U hU) t = handoff e t := by
  unfold handoff
  apply Finset.sum_congr rfl
  intro v _
  have ha : (S.position (v,false)).val+1 ≤ 2*S.visits := by
    have := (S.position (v,false)).isLt; omega
  have hb : (S.position (v,true)).val+1 ≤ 2*S.visits := by
    have := (S.position (v,true)).isLt; omega
  unfold carrierEnergy
  rw [finalBodyContact_run_before e U hU t _ hb,finalBodyContact_run_before e U hU t _ ha]
  rfl

end ScheduleLaw.Blueprint
