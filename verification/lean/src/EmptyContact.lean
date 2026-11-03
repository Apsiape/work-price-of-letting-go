import RetainedEffect
import IdleTester
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! Body-only contacts and the exact zero-visit operational maps. All
constants are derived from the actual extension gates and source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

def payloadZero (I : Inventory) : Payload I := fun c => ⟨0,I.dim_pos c⟩

theorem restricted_empty_eq (I : Inventory) (p q : Restricted I ∅) : p = q := by
  funext c
  exact False.elim (Finset.notMem_empty c.val c.property)

def emptyBodyCoordinates (I : Inventory) (b : ℕ) : Fin b ≃ Fin b × Restricted I ∅ where
  toFun i := (i,restrictPayload I ∅ (payloadZero I))
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := Prod.ext rfl (restricted_empty_eq I _ _)

def emptyBodyMatrix (I : Inventory) (b : ℕ) (U : Mat (Fin b × Payload I)) : Mat (Fin b) :=
  fun i j => U (i,payloadZero I) (j,payloadZero I)

theorem local_empty_tensor (I : Inventory) (b : ℕ) (U : Mat (Fin b × Payload I))
    (hU : LocalOn I b ∅ U) : U = emptyBodyMatrix I b U ⊗ₖ (1 : Mat (Payload I)) := by
  obtain ⟨V,hV,hUV⟩ := hU
  have hr (p : Payload I) : restrictPayload I ∅ p = restrictPayload I ∅ (payloadZero I) :=
    restricted_empty_eq I _ _
  have hu (p q : Payload I) : restrictPayload I (∅ : Finset (Fin I.count))ᶜ p =
      restrictPayload I (∅ : Finset (Fin I.count))ᶜ q ↔ p = q := by
    rw [restriction_eq_iff]
    simp only [Finset.compl_empty,Finset.mem_univ,forall_const]
    exact funext_iff.symm
  ext i j
  rw [hUV]
  simp only [emptyBodyMatrix,kroneckerMap_apply,one_apply,hUV,hr,hu,if_true,mul_one]

theorem emptyBodyMatrix_unitary (I : Inventory) (b : ℕ) (U : Mat (Fin b × Payload I))
    (hU : LocalOn I b ∅ U) : IsUnitary (emptyBodyMatrix I b U) := by
  obtain ⟨V,hV,hUV⟩ := hU
  have he : emptyBodyMatrix I b U = V.submatrix (emptyBodyCoordinates I b)
      (emptyBodyCoordinates I b) := by
    ext i j
    simp [emptyBodyMatrix,hUV,emptyBodyCoordinates]
  rw [he]
  exact unitary_submatrix _ hV

theorem held_zero_visits {I : Inventory} (S : Schedule I) (hz : S.visits = 0) (k : Cut S) :
    held S k = ∅ := by
  haveI : IsEmpty (Fin S.visits) := by rw [hz]; infer_instance
  simp [held]

theorem initial_body_marginal {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : partialRight (initialState e t) = e.source.matrix := by
  have ht := (initialState_density e t).2
  rw [initialState,trace_kronecker,e.source.normalized,one_mul] at ht
  rw [initialState,partialRight_kron,ht,one_smul]

theorem body_step_empty {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) (hk : held S k = ∅)
    (ρ : Mat (Global e r)) :
    partialRight (evolve (jointGate e t k) ρ) =
      evolve (emptyBodyMatrix I e.b (e.gate k)) (partialRight ρ) := by
  have hl := e.gate_local k
  rw [hk] at hl
  have hD := congrArg (liftDeviceObservable e r) (local_empty_tensor I e.b (e.gate k) hl)
  rw [liftDevice_body] at hD
  rw [jointGate_as_product,evolve_mul,tester_preserves_body,hD,partialRight_evolve_kron_one]

def zeroVisitBody {I : Inventory} {S : Schedule I} (e : Extension S) : Mat (Fin e.b) :=
  evolve (emptyBodyMatrix I e.b (e.gate ⟨0,by omega⟩)) e.source.matrix

theorem bodyOutput_zero_visits {I : Inventory} {S : Schedule I} (e : Extension S)
    (hz : S.visits = 0) {r : ℕ} (t : Tester S r) : bodyOutput e t = zeroVisitBody e := by
  have hn : 2*S.visits+1 = 1 := by omega
  unfold bodyOutput finalState
  rw [hn,run,dif_pos (by omega),body_step_empty e t _ (held_zero_visits S hz _)]
  exact congrArg (evolve _) (initial_body_marginal e t)

theorem handoff_zero_visits {I : Inventory} {S : Schedule I} (e : Extension S)
    (hz : S.visits = 0) {r : ℕ} (t : Tester S r) : handoff e t = 0 := by
  haveI : IsEmpty (Fin S.visits) := by rw [hz]; infer_instance
  exact Finset.sum_eq_zero (fun v _ => isEmptyElim v)

def zeroVisitBodyAffine {I : Inventory} {S : Schedule I} (e : Extension S) :
    PrefixMatrices S →ᵃ[ℝ] Mat (Fin e.b) :=
  AffineMap.const ℝ (PrefixMatrices S) (zeroVisitBody e)

def zeroVisitEnergyAffine {I : Inventory} {S : Schedule I} : PrefixMatrices S →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (PrefixMatrices S) 0

theorem zero_visit_operational_maps {I : Inventory} {S : Schedule I} (e : Extension S)
    (hz : S.visits = 0) {r : ℕ} (t : Tester S r) :
    zeroVisitBodyAffine e (fun b => prefixGram b t) = bodyOutput e t ∧
      zeroVisitEnergyAffine (S := S) (fun b => prefixGram b t) = handoff e t :=
  ⟨(bodyOutput_zero_visits e hz t).symm,(handoff_zero_visits e hz t).symm⟩

theorem zero_visit_body_density {I : Inventory} {S : Schedule I} (e : Extension S)
    (hz : S.visits = 0) : (zeroVisitBody e).PosSemidef ∧ (zeroVisitBody e).trace = 1 := by
  rw [← bodyOutput_zero_visits e hz (idleTester S)]
  exact bodyOutput_density e (idleTester S)

theorem zero_visit_score_constant {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    (hz : S.visits = 0) {r : ℕ} (t : Tester S r) :
    score β e t = (entropy (zeroVisitBody e) - entropy e.source.matrix) / β := by
  rw [score,bodyOutput_zero_visits e hz t,handoff_zero_visits e hz t,add_zero]

end ScheduleLaw.History
