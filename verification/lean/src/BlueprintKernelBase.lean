import BlueprintWireReadout

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

/-- An inert purifier may have different indices on the two sides. -/
theorem purifier_block_evolution {a f : Type} [Fintype a] [Fintype f]
    [DecidableEq f] (U : Mat a) (v : a × f → ℂ) (p q : f) :
    (pureMatrix ((U ⊗ₖ (1 : Mat f)) *ᵥ v)).submatrix (fun i => (i,p)) (fun j => (j,q)) =
      U * (pureMatrix v).submatrix (fun i => (i,p)) (fun j => (j,q)) * Uᴴ := by
  have hv (i : a) (k : f) : ((U ⊗ₖ (1 : Mat f)) *ᵥ v) (i,k) =
      (U *ᵥ (fun j => v (j,k))) i := by
    simp [mulVec,dotProduct,Fintype.sum_prod_type,kroneckerMap_apply,one_apply,
      mul_ite,ite_mul]
  have he := cross_outer_transform U U (fun i => v (i,p)) (fun i => v (i,q))
  ext i j
  simpa only [submatrix_apply,pureMatrix,hv,crossOuter] using (congrFun₂ he i j).symm

theorem sourceBlock_history {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (f g : Fin e.f) :
    sourceBlock e t n f g = evolve (historyUnitary e t n) (sourceCrossInitial e t f g) := by
  have hc : (pureMatrix (purifiedInitial e t)).submatrix (fun i => (i,f))
      (fun j => (j,g)) = sourceCrossInitial e t f g := by
    ext i j
    simp only [submatrix_apply,pureMatrix,purifiedInitial,sourceCrossInitial,crossOuter,
      initialTesterMatrix,kroneckerMap_apply,star_mul]
    ring
  rw [sourceBlock,purifiedVector,purifier_block_evolution,hc]
  rfl

theorem sourceBlock_step {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (hn : n < 2*S.visits+1) (f g : Fin e.f) :
    sourceBlock e t (n+1) f g = evolve (jointGate e t ⟨n,hn⟩) (sourceBlock e t n f g) := by
  rw [sourceBlock_history,historyUnitary,dif_pos hn,evolve_mul,sourceBlock_history]

def initialResponse {I : Inventory} {S : Schedule I} (e : Extension S) (f : Fin e.f) :
    Matrix (Fin e.b) (Recorder.Stock S) ℂ :=
  emptyBodyMatrix I e.b (e.gate ⟨0,by omega⟩) * sourceKernel e f

def initialCutKernel {I : Inventory} {S : Schedule I} (e : Extension S) (f : Fin e.f) :
    CutKernel e ⟨0,by omega⟩ := fun i j => initialResponse e f i.1 j.1

theorem initial_kernel_lift {I : Inventory} {S : Schedule I} (e : Extension S)
    (f : Fin e.f) (r : ℕ) :
    kernelLift e ⟨0,by omega⟩ r (initialCutKernel e f) =
      initialResponse e f ⊗ₖ (1 : Mat (Payload I × Fin r)) := by
  have he (p q : Payload I) : restrictPayload I (held S ⟨0,by omega⟩)ᶜ p =
      restrictPayload I (held S ⟨0,by omega⟩)ᶜ q ↔ p=q := by
    rw [restriction_eq_iff,held_initial]
    simp only [Finset.compl_empty,Finset.mem_univ,true_implies]
    exact funext_iff.symm
  ext i j
  simp only [kernelLift,initialCutKernel,he,kroneckerMap_apply,one_apply,Prod.ext_iff]

theorem raw_first_product {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) :
    rawState t 1 = pureMatrix (Recorder.epr (a := Recorder.Inputs S)) ⊗ₖ
      preparedTesterMatrix t := by
  have hg : (Recorder.extension S).gate ⟨0,by omega⟩ = 1 := by
    apply Recorder.gate_elsewhere
    intro v hv
    have he := congrArg Fin.val hv
    simp only [Recorder.arrivalCut] at he
    omega
  have hz : zeroVisitBody (Recorder.extension S) = (Recorder.extension S).source.matrix := by
    unfold zeroVisitBody
    rw [hg]
    have he : emptyBodyMatrix I (Recorder.extension S).b
        (1 : Mat (Fin (Recorder.extension S).b × Payload I)) = 1 := by
      ext i j
      simp [emptyBodyMatrix,Matrix.one_apply]
    rw [he]
    simp [evolve]
  rw [rawState,initial_contact_product,hz]
  ext i j
  simp [actual,Recorder.extension,Recorder.source,Recorder.initialVector,
    pureMatrix,kroneckerMap_apply]

/-- The schedule-wide kernel invariant at cut zero, before any endpoint.
The response is chosen before the tester dimension and retains every purifier block. -/
theorem initial_kernel_contraction {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∀ (r : ℕ) (t : Tester S r) (f g : Fin e.f),
      sourceBlock e t 1 f g =
        kernelLift e ⟨0,by omega⟩ r (initialCutKernel e f) * rawState t 1 *
          (kernelLift e ⟨0,by omega⟩ r (initialCutKernel e g))ᴴ := by
  intro r t f g
  have hl := e.gate_local ⟨0,by omega⟩
  rw [held_initial S] at hl
  have hD := congrArg (liftDeviceObservable e r)
    (local_empty_tensor I e.b (e.gate ⟨0,by omega⟩) hl)
  rw [liftDevice_body] at hD
  rw [sourceBlock_history,historyUnitary,historyUnitary,dif_pos (by omega)]
  simp only [Matrix.mul_one]
  rw [jointGate_as_product,hD]
  rw [initial_kernel_lift,initial_kernel_lift,raw_first_product]
  change evolve (((1 : Mat (Fin e.b)) ⊗ₖ _)*(_ ⊗ₖ (1 : Mat (Payload I × Fin r))))
    (sourceCrossInitial e t f g) = _
  simp only [sourceCrossInitial,evolve,initialResponse,conjTranspose_kronecker,
    conjTranspose_mul,conjTranspose_one,← mul_kronecker_mul,one_mul,mul_one]
  rw [← sourceKernel_initial_cross]
  simp only [preparedTesterMatrix,evolve,Matrix.mul_assoc]

theorem zero_visit_kernel_contraction {I : Inventory} {S : Schedule I} (e : Extension S)
    (hz : S.visits=0) :
    ∃ K : (k : Cut S) → Fin e.f → CutKernel e k,
      ∀ (r : ℕ) (t : Tester S r) (k : Cut S) (f g : Fin e.f),
        sourceBlock e t (k.val+1) f g =
          kernelLift e k r (K k f) * rawState t (k.val+1) *
            (kernelLift e k r (K k g))ᴴ := by
  refine ⟨fun _ f i j => initialResponse e f i.1 j.1,?_⟩
  intro r t k f g
  have hk : k=(⟨0,by omega⟩ : Cut S) := Fin.ext (by have := k.isLt; omega)
  subst k
  exact initial_kernel_contraction e r t f g

#print axioms purifier_block_evolution
#print axioms sourceBlock_history
#print axioms sourceBlock_step
#print axioms initialResponse
#print axioms initialCutKernel
#print axioms initial_kernel_lift
#print axioms raw_first_product
#print axioms initial_kernel_contraction
#print axioms zero_visit_kernel_contraction
end ScheduleLaw.Blueprint
