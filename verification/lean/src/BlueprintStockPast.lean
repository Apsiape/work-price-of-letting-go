import BlueprintStockRecovery

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History History.Wire

/-- Not-yet-arrived visit pairs remain jointly in their initialized pure
state. The assertion includes future repeated loans of the same carrier. -/
theorem future_pairs_pure {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) : chi t n (arrived S n)ᶜ (arrived S n)ᶜ=
      pureMatrix (Recorder.epr (a := Registers S (arrived S n)ᶜ)) := by
  have hstage : ∀ m ≤ n, chi t m (arrived S n)ᶜ (arrived S n)ᶜ=
      chi t 0 (arrived S n)ᶜ (arrived S n)ᶜ := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [chi_step_old_inputs S t m]
      · exact ih (by omega)
      · intro v hv hmem
        have ha : v ∈ arrived S n := by
          simp only [arrived,Finset.mem_filter,Finset.mem_univ,true_and]
          change (S.position (v,false)).val+1=m at hv
          omega
        exact (Finset.mem_compl.mp hmem) ha
  rw [hstage n le_rfl,chi_rawMarginal]
  exact initial_pair_marginal S t _

theorem future_pairs_factor {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) :
    (rawState t n).submatrix (recordCoordinates S r (arrived S n)ᶜ (arrived S n)ᶜ).symm
      (recordCoordinates S r (arrived S n)ᶜ (arrived S n)ᶜ).symm=
      pureMatrix (Recorder.epr (a := Registers S (arrived S n)ᶜ)) ⊗ₖ
        partialLeft ((rawState t n).submatrix
          (recordCoordinates S r (arrived S n)ᶜ (arrived S n)ᶜ).symm
          (recordCoordinates S r (arrived S n)ᶜ (arrived S n)ᶜ).symm) := by
  let C := recordCoordinates S r (arrived S n)ᶜ (arrived S n)ᶜ
  let ψ := fun x => amplitudes t Recorder.epr n (C.symm x)
  have hp : (rawState t n).submatrix C.symm C.symm=pureMatrix ψ := by
    rw [rawState,run_amplitudes]
    rfl
  have ht : (pureMatrix ψ).trace=1 := by
    rw [← hp,submatrix_trace_equiv,rawState,submatrix_trace_equiv]
    exact (run_density (Recorder.extension S) t n).2
  rw [pureMatrix_trace] at ht
  have hn : ∑ x, Complex.normSq (ψ x)=1 := congrArg Complex.re ht
  have hm : partialRight (pureMatrix ψ)=pureMatrix (Recorder.epr (a := Registers S (arrived S n)ᶜ)) := by
    rw [← hp]
    change chi t n (arrived S n)ᶜ (arrived S n)ᶜ=_
    exact future_pairs_pure S t n
  rw [hp]
  exact pure_marginal_factor ψ _ hn Recorder.epr_normalized hm

def terminalPastReadout {I : Inventory} (S : Schedule I) (n : ℕ) :
    Mat (Recorder.Stock S) →ₗ[ℂ] Mat (Record S (arrived S n) (arrived S n)) where
  toFun A := partialRight (A.submatrix (stockPartition S (arrived S n) (arrived S n)).symm
    (stockPartition S (arrived S n) (arrived S n)).symm)
  map_add' A B := by
    simp only [submatrix_add]
    ext i j
    exact Finset.sum_add_distrib
  map_smul' c A := by
    ext i j
    change (∑ k, c*A _ _)=c*∑ k,A _ _
    exact (Finset.mul_sum _ _ _).symm

theorem terminalPastReadout_actual {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (n : ℕ) (hn : n ≤ 2*S.visits+1) :
    terminalPastReadout S n (terminalStock t)=chi t n (arrived S n) (arrived S n) := by
  rw [← recorded_inputs_frozen S t n (2*S.visits+1) hn]
  rw [chi_rawMarginal,rawMarginal_body]
  rfl

def doubleComplementRegisters {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Registers S V ≃ Registers S Vᶜᶜ where
  toFun a w := a ⟨w.val,by simpa only [compl_compl] using w.property⟩
  invFun a w := a ⟨w.val,by simpa only [compl_compl] using w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stock_complement_inverse {I : Inventory} (S : Schedule I)
    (V : Finset (Fin S.visits)) (p : Record S V V) (q : Record S Vᶜ Vᶜ) :
    (stockPartition S Vᶜ Vᶜ).symm
      (q,(Equiv.prodCongr (doubleComplementRegisters S V) (doubleComplementRegisters S V)) p)=
        (stockPartition S V V).symm (p,q) := by
  apply Prod.ext <;> funext v <;> by_cases hv : v ∈ V <;>
    simp [stockPartition,registerPartition,doubleComplementRegisters,hv]

theorem record_rest_marginal {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) (V : Finset (Fin S.visits)) :
    partialRight (partialLeft ((rawState t n).submatrix
      (recordCoordinates S r V V).symm (recordCoordinates S r V V).symm))=
        chi t n Vᶜ Vᶜ := by
  let E := Equiv.prodCongr (doubleComplementRegisters S V) (doubleComplementRegisters S V)
  rw [chi_rawMarginal,rawMarginal_body]
  ext i j
  change (∑ z : Payload I × Fin r, ∑ p : Record S V V,
    rawState t n ((stockPartition S V V).symm (p,i),z)
      ((stockPartition S V V).symm (p,j),z))=
    ∑ q : Record S Vᶜᶜ Vᶜᶜ, ∑ z : Payload I × Fin r,
      rawState t n ((stockPartition S Vᶜ Vᶜ).symm (i,q),z)
        ((stockPartition S Vᶜ Vᶜ).symm (j,q),z)
  rw [Finset.sum_comm]
  have h := Equiv.sum_comp E (fun q => ∑ z : Payload I × Fin r,
    rawState t n ((stockPartition S Vᶜ Vᶜ).symm (i,q),z)
      ((stockPartition S Vᶜ Vᶜ).symm (j,q),z))
  simpa only [E,stock_complement_inverse] using h

theorem stock_future_product {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) :
    (partialRight (rawState t n)).submatrix
      (stockPartition S (arrived S n)ᶜ (arrived S n)ᶜ).symm
      (stockPartition S (arrived S n)ᶜ (arrived S n)ᶜ).symm=
      pureMatrix (Recorder.epr (a := Registers S (arrived S n)ᶜ)) ⊗ₖ
        chi t n (arrived S n)ᶜᶜ (arrived S n)ᶜᶜ := by
  let V := (arrived S n)ᶜ
  let X := (rawState t n).submatrix (recordCoordinates S r V V).symm
    (recordCoordinates S r V V).symm
  have hf : X=pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ partialLeft X :=
    future_pairs_factor S t n
  have hr := record_rest_marginal S t n V
  ext i j
  change (∑ z : Payload I × Fin r, X (i.1,(i.2,z)) (j.1,(j.2,z)))=_
  rw [hf]
  simp only [kroneckerMap_apply,← Finset.mul_sum]
  have h := congrFun₂ hr i.2 j.2
  exact congrArg (pureMatrix (Recorder.epr (a := Registers S V)) i.1 j.1*·) h

def terminalStockAtLinear {I : Inventory} (S : Schedule I) (n : ℕ) :
    Mat (Recorder.Stock S) →ₗ[ℂ] Mat (Recorder.Stock S) where
  toFun A :=
    let V := (arrived S n)ᶜ
    (pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
      partialRight (A.submatrix (stockPartition S Vᶜ Vᶜ).symm
        (stockPartition S Vᶜ Vᶜ).symm)).submatrix (stockPartition S V V) (stockPartition S V V)
  map_add' A B := by
    ext i j
    simp only [submatrix_apply,submatrix_add,kroneckerMap_apply,Pi.add_apply,Matrix.add_apply,partialRight,
      Finset.sum_add_distrib,mul_add]
  map_smul' c A := by
    ext i j
    simp only [submatrix_apply,submatrix_smul,kroneckerMap_apply,Pi.smul_apply,Matrix.smul_apply,RingHom.id_apply,smul_eq_mul,
      partialRight,← Finset.mul_sum]
    ring

theorem terminalStockAtLinear_actual {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (n : ℕ) (hn : n ≤ 2*S.visits+1) :
    terminalStockAtLinear S n (terminalStock t)=partialRight (rawState t n) := by
  let V := (arrived S n)ᶜ
  have hp : chi t (2*S.visits+1) Vᶜ Vᶜ=chi t n Vᶜ Vᶜ := by
    dsimp only [V]
    rw [compl_compl]
    exact recorded_inputs_frozen S t n (2*S.visits+1) hn (arrived S n)
  rw [chi_rawMarginal,rawMarginal_body] at hp
  have hf : (partialRight (rawState t n)).submatrix (stockPartition S V V).symm
      (stockPartition S V V).symm=pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
        chi t n Vᶜ Vᶜ := stock_future_product S t n
  ext i j
  have h := congrFun₂ hf ((stockPartition S V V) i) ((stockPartition S V V) j)
  simp only [submatrix_apply,Equiv.symm_apply_apply] at h
  change (pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
      partialRight ((terminalStock t).submatrix (stockPartition S Vᶜ Vᶜ).symm
        (stockPartition S Vᶜ Vᶜ).symm)) ((stockPartition S V V) i) ((stockPartition S V V) j)=_
  rw [show partialRight ((terminalStock t).submatrix (stockPartition S Vᶜ Vᶜ).symm
      (stockPartition S Vᶜ Vᶜ).symm)=chi t n Vᶜ Vᶜ from hp]
  exact h.symm

#print axioms future_pairs_pure
#print axioms future_pairs_factor
#print axioms terminalPastReadout
#print axioms terminalPastReadout_actual
#print axioms doubleComplementRegisters
#print axioms stock_complement_inverse
#print axioms record_rest_marginal
#print axioms stock_future_product
#print axioms terminalStockAtLinear
#print axioms terminalStockAtLinear_actual
end ScheduleLaw.Blueprint
