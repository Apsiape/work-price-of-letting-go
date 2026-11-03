import BlueprintContracts

/-! Reconstruct the complete terminal recorder stock from the original last
prefix. The remaining partners are flat jointly with that prefix; all
visit registers, including repeated loans, remain in the stock. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

def completeRegisters {I : Inventory} (S : Schedule I) (A : Finset (Fin S.visits))
    (hA : A=Finset.univ) : Recorder.Inputs S ≃ Registers S A where
  toFun a v := a v.val
  invFun a v := a ⟨v,by rw [hA]; simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fullStockRecord {I : Inventory} (S : Schedule I) (A : Finset (Fin S.visits))
    (hA : A=Finset.univ) : Recorder.Stock S ≃ Record S A Finset.univ :=
  Equiv.prodCongr (completeRegisters S A hA) (completeRegisters S Finset.univ rfl)

theorem rawStock_body {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (n : ℕ) :
    partialRight (rawState t n) = (partialRight (run (Recorder.extension S) t n)).submatrix
      (Recorder.stockFin S) (Recorder.stockFin S) := by
  unfold rawState actual
  exact partialRight_prod_equiv _ _ _

theorem full_record_chi {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (n : ℕ) (A : Finset (Fin S.visits)) (hA : A=Finset.univ) :
    (chi t n A Finset.univ).submatrix (fullStockRecord S A hA) (fullStockRecord S A hA) =
      partialRight (rawState t n) := by
  have hmem (v : Fin S.visits) : v ∈ A := by rw [hA]; simp
  letI : Subsingleton (Registers S Aᶜ) := ⟨by
    intro a b
    funext v
    have hv : v.val ∈ A := hmem v.val
    exact False.elim ((Finset.mem_compl.mp v.property) hv)⟩
  letI : Subsingleton (Registers S (Finset.univ : Finset (Fin S.visits))ᶜ) := ⟨by
    intro a b
    funext v
    exact False.elim ((Finset.mem_compl.mp v.property) (Finset.mem_univ _))⟩
  letI : Nonempty (Record S Aᶜ (Finset.univ : Finset (Fin S.visits))ᶜ) :=
    ⟨(fun v => ⟨0,I.dim_pos (S.carrier v.val)⟩,fun v => ⟨0,I.dim_pos (S.carrier v.val)⟩)⟩
  letI : Unique (Record S Aᶜ (Finset.univ : Finset (Fin S.visits))ᶜ) :=
    { default := Classical.choice inferInstance
      uniq := fun _ => Subsingleton.elim _ _ }
  have hinv (i : Recorder.Stock S) (q : Record S Aᶜ (Finset.univ : Finset (Fin S.visits))ᶜ) :
      (stockPartition S A Finset.univ).symm (fullStockRecord S A hA i,q)=i := by
    apply Prod.ext <;> funext v
    · have hv : v ∈ A := by rw [hA]; simp
      simp [stockPartition,registerPartition,fullStockRecord,completeRegisters,hv]
    · simp [stockPartition,registerPartition,fullStockRecord,completeRegisters]
  rw [chi_rawMarginal,rawMarginal_body]
  apply Matrix.ext
  intro i j
  change (∑ q, partialRight (rawState t n)
    ((stockPartition S A Finset.univ).symm (fullStockRecord S A hA i,q))
    ((stockPartition S A Finset.univ).symm (fullStockRecord S A hA j,q))) = _
  simp only [hinv,Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_smul]

def finalStockFrame {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    Recorder.Stock S ≃ Registers S (Finset.univ \ released S (recordTime (lastInputBurst S h))) ×
      PrefixSpace (lastInputBurst S h) :=
  (fullStockRecord S _ (last_inputs_complete S h)).trans
    (outputRefinement S _ _ Finset.univ (Finset.subset_univ _))

theorem final_partners_active {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    Finset.univ \ released S (recordTime (lastInputBurst S h)) ⊆
      activeVisits S (prefixCut (lastInputBurst S h)) := by
  intro v hv
  have ha := all_inputs_before_last S h v
  have hn := (Finset.mem_sdiff.mp hv).2
  have hr : ¬(S.position (v,true)).val+1 < recordTime (lastInputBurst S h) := by
    simpa only [released,Finset.mem_filter,Finset.mem_univ,true_and] using hn
  simp only [activeVisits,Finset.mem_filter,Finset.mem_univ,true_and,prefixCut]
  change (S.position (v,false)).val ≤ (last (lastInputBurst S h).val).val at ha
  unfold recordTime at hr
  omega

theorem terminal_stock_from_chi {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) :
    terminalStock t = (((outputDimension S (Finset.univ \ released S (recordTime (lastInputBurst S h))) : ℂ)⁻¹ •
      (1 : Mat (Registers S (Finset.univ \ released S (recordTime (lastInputBurst S h)))))) ⊗ₖ
        prefixChi (lastInputBurst S h) t).submatrix (finalStockFrame S h) (finalStockFrame S h) := by
  let b := lastInputBurst S h
  let A := arrived S (recordTime b)
  let O := released S (recordTime b)
  have hf := fresh_selected_record S t (prefixCut b) A O Finset.univ (Finset.subset_univ _)
    (final_partners_active S h)
  have hp : terminalStock t = partialRight (rawState t (recordTime b)) := by
    unfold terminalStock
    rw [rawStock_body,rawStock_body,body_after_last S h t _ (recordTime_bound _)]
  rw [hp]
  apply Matrix.ext
  intro i j
  have hv := congrFun₂ hf
    ((outputRefinement S A O Finset.univ (Finset.subset_univ _)) (fullStockRecord S A (last_inputs_complete S h) i))
    ((outputRefinement S A O Finset.univ (Finset.subset_univ _)) (fullStockRecord S A (last_inputs_complete S h) j))
  have hc := congrFun₂ (full_record_chi S t (recordTime b) A (last_inputs_complete S h)) i j
  simp only [withNewOutputsFirst,Matrix.submatrix_apply,Equiv.symm_apply_apply,prefixCut_time] at hv
  exact hc.symm.trans hv

def terminalStockLinear {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    PrefixMatrices S →ₗ[ℝ] Mat (Recorder.Stock S) where
  toFun Z :=
    let b := lastInputBurst S h
    let V := Finset.univ \ released S (recordTime b)
    let C : Mat (Registers S V) := (outputDimension S V : ℂ)⁻¹ • 1
    (C ⊗ₖ ((prefixDimension b : ℂ)⁻¹ • Z b)).submatrix (finalStockFrame S h) (finalStockFrame S h)
  map_add' Z W := by
    simp only [Pi.add_apply,smul_add,kronecker_add,Matrix.submatrix_add]
  map_smul' c Z := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply,kroneckerMap_apply,Matrix.smul_apply,Pi.smul_apply,
      Complex.real_smul,smul_eq_mul,RingHom.id_apply]
    ring

theorem terminalStockLinear_actual {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) :
    terminalStockLinear S h (fun b => prefixGram b t)=terminalStock t := by
  rw [terminal_stock_from_chi S h t,prefix_recorder_identity]
  rfl

#print axioms completeRegisters
#print axioms fullStockRecord
#print axioms rawStock_body
#print axioms full_record_chi
#print axioms finalStockFrame
#print axioms final_partners_active
#print axioms terminal_stock_from_chi
#print axioms terminalStockLinear
#print axioms terminalStockLinear_actual
end ScheduleLaw.Blueprint
