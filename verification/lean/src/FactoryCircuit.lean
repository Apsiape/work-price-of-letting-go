import FinalBodyContact
import PrefixPurification
import BlueprintContracts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCircuit
open History

/-- Every factory register is in the retained body. Its purification is inert. -/
def bodyCircuit {I : Inventory} (S : Schedule I) {n : ℕ} (hn : 0<n)
    (ρ : Density (Fin n)) (U : Mat (Fin n)) (hU : IsUnitary U) : Extension S where
  b := n
  b_pos := hn
  source := ρ
  f := n
  f_pos := hn
  purification := ρ.toMState.purify.vec
  purification_norm := by
    simpa only [Complex.normSq_eq_norm_sq,Ket.coe_fun_eq] using ρ.toMState.purify.normalized
  purification_reduces := density_purification_matrix ρ.toMState
  gate _ := U ⊗ₖ (1 : Mat (Payload I))
  unitary _ := unitary_kron hU (by constructor <;> simp)
  gate_local _ := body_tensor_local I n _ U hU

theorem body_matrix {I : Inventory} (S : Schedule I) {n : ℕ} (hn : 0<n)
    (ρ : Density (Fin n)) (U : Mat (Fin n)) (hU : IsUnitary U) :
    emptyBodyMatrix I n ((bodyCircuit S hn ρ U hU).gate ⟨0,by omega⟩) = U := by
  ext i j
  simp [emptyBodyMatrix,bodyCircuit]

theorem output {I : Inventory} (S : Schedule I) (hS : S.visits=0) {n : ℕ} (hn : 0<n)
    (ρ : Density (Fin n)) (U : Mat (Fin n)) (hU : IsUnitary U)
    {r : ℕ} (t : Tester S r) :
    bodyOutput (bodyCircuit S hn ρ U hU) t = evolve U ρ.matrix := by
  rw [bodyOutput_zero_visits _ hS]
  unfold zeroVisitBody
  rw [body_matrix]
  rfl

/-- The exact final joint state remains a product with every coherent tester
 when the schedule has no external visits. This is stronger than a body marginal. -/
theorem final_product {I : Inventory} (S : Schedule I) (hS : S.visits=0) {n : ℕ} (hn : 0<n)
    (ρ : Density (Fin n)) (U : Mat (Fin n)) (hU : IsUnitary U)
    {r : ℕ} (t : Tester S r) :
    ∃ σ : Density (Payload I × Fin r),
      finalState (bodyCircuit S hn ρ U hU) t = evolve U ρ.matrix ⊗ₖ σ.matrix := by
  let e := bodyCircuit S hn ρ U hU
  let k : Cut S := ⟨0,by omega⟩
  let T := (t.gate k).submatrix (Equiv.prodComm (Payload I) (Fin r))
    (Equiv.prodComm (Payload I) (Fin r))
  let v := fun x : Payload I × Fin r => t.initial (x.2,x.1)
  have hv : ∑ i,Complex.normSq (v i)=1 := by
    exact (Equiv.sum_comp (Equiv.prodComm (Payload I) (Fin r))
      (fun x => Complex.normSq (t.initial x))).trans t.normalized
  let σ0 : Density (Payload I × Fin r) :=
    ⟨pureMatrix v,pureMatrix_positive _,by rw [pureMatrix_trace,hv]; rfl⟩
  obtain ⟨hσ,hσt⟩ := evolve_density T σ0.matrix
    (unitary_submatrix _ (t.unitary k)) σ0.positive σ0.normalized
  let σ : Density (Payload I × Fin r) := ⟨evolve T σ0.matrix,hσ,hσt⟩
  refine ⟨σ,?_⟩
  have hsteps : 2*S.visits+1=1 := by omega
  change run e t (2*S.visits+1) = _
  rw [hsteps,run,dif_pos (by omega)]
  have hj : jointGate e t k = U ⊗ₖ T := by
    rw [jointGate_as_product]
    change ((1 : Mat (Fin e.b)) ⊗ₖ T) * liftDeviceObservable e r (U ⊗ₖ 1) = _
    rw [liftDevice_body,← mul_kronecker_mul,one_mul,mul_one]
  change evolve (jointGate e t k) (initialState e t) = _
  rw [hj]
  simp only [evolve,initialState,e,bodyCircuit,conjTranspose_kronecker,
    ← mul_kronecker_mul]
  rfl

end ScheduleLaw.Blueprint.FactoryCircuit
