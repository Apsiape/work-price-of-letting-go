import MarginalRefinement

/-! Passing the complete-stock fresh-partner factorization to an arbitrary
retained input/output record, in the new-output-first convention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

theorem tensor_marginal_route {x a b z w : Type} [Fintype z] [Fintype w]
    (coarse : x ≃ a × z) (fine : x ≃ (a × b) × w) (env : z ≃ b × w)
    (hr : coarse.trans (Equiv.prodCongr (Equiv.refl _) env) =
      fine.trans (Equiv.prodAssoc _ _ _)) (ρ : Mat x) (A : Mat a) (B : Mat z)
    (hf : ρ.submatrix coarse.symm coarse.symm = A ⊗ₖ B) :
    partialRight (ρ.submatrix fine.symm fine.symm) =
      A ⊗ₖ partialRight (B.submatrix env.symm env.symm) := by
  have he (i : a) (j : b) (k : w) :
      fine.symm ((i,j),k) = coarse.symm (i,env.symm (j,k)) := by
    apply (coarse.trans (Equiv.prodCongr (Equiv.refl _) env)).injective
    rw [hr]
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodAssoc_apply,
      Equiv.prodCongr_apply,Equiv.refl_apply]
    have ht := congrArg (fun e => e (coarse.symm (i,env.symm (j,k)))) hr
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodCongr_apply,
      Equiv.refl_apply,Prod.map_apply,Equiv.prodAssoc_apply] using ht
  ext i j
  change (∑ k, ρ (fine.symm (i,k)) (fine.symm (j,k))) = _
  simp only [he]
  change (∑ k, (ρ.submatrix coarse.symm coarse.symm)
      (i.1,env.symm (i.2,k)) (j.1,env.symm (j.2,k))) = _
  rw [hf]
  simp only [kroneckerMap_apply,partialRight,submatrix_apply,Finset.mul_sum]

theorem nested_left_partial_trace {x a b z w : Type} [Fintype a] [Fintype z] [Fintype w]
    (coarse : x ≃ b × z) (fine : x ≃ (a × b) × w) (env : z ≃ a × w)
    (hr : coarse.trans (Equiv.prodCongr (Equiv.refl _) env) =
      (fine.trans (Equiv.prodCongr (Equiv.prodComm a b) (Equiv.refl _))).trans
        (Equiv.prodAssoc _ _ _)) (ρ : Mat x) :
    partialLeft (partialRight (ρ.submatrix fine.symm fine.symm)) =
      partialRight (ρ.submatrix coarse.symm coarse.symm) :=
  nested_partial_trace coarse
    (fine.trans (Equiv.prodCongr (Equiv.prodComm a b) (Equiv.refl _))) env hr ρ

def outputEnvironmentRefinement {I : Inventory} (S : Schedule I)
    (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Record S Aᶜ Vᶜ ≃ Registers S (W \ V) × Record S Aᶜ Wᶜ where
  toFun x := ((complementRefinement S V W hVW x.2).1,(x.1,(complementRefinement S V W hVW x.2).2))
  invFun x := (x.2.1,(complementRefinement S V W hVW).symm (x.1,x.2.2))
  left_inv x := by dsimp only; rw [Equiv.symm_apply_apply]
  right_inv x := by dsimp only; rw [Equiv.apply_symm_apply]

theorem output_refinement_route {I : Inventory} (S : Schedule I)
    (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    (stockPartition S A V).trans (Equiv.prodCongr (Equiv.refl _)
      (outputEnvironmentRefinement S A V W hVW)) =
      (((stockPartition S A W).trans
        (Equiv.prodCongr (outputRefinement S A V W hVW) (Equiv.refl _))).trans
          (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _))).trans
            (Equiv.prodAssoc _ _ _) := by
  apply Equiv.ext
  intro x
  rfl

theorem traceNewOutputs_stock {I : Inventory} (S : Schedule I)
    (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W) (ρ : Mat (Recorder.Stock S)) :
    partialLeft (withNewOutputsFirst S A V W hVW
      (partialRight (ρ.submatrix (stockPartition S A W).symm (stockPartition S A W).symm))) =
    partialRight (ρ.submatrix (stockPartition S A V).symm (stockPartition S A V).symm) := by
  have h := nested_left_partial_trace (stockPartition S A V)
    ((stockPartition S A W).trans
      (Equiv.prodCongr (outputRefinement S A V W hVW) (Equiv.refl _)))
    (outputEnvironmentRefinement S A V W hVW) (output_refinement_route S A V W hVW) ρ
  rw [withNewOutputsFirst]
  rw [← partialRight_prod_equiv (outputRefinement S A V W hVW).symm (Equiv.refl _)]
  exact h

def relativePartnerPartition {I : Inventory} (S : Schedule I)
    (V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Registers S (W \ V)ᶜ ≃ Registers S V × Registers S Wᶜ where
  toFun x := (fun v => x ⟨v.val,by simp [v.property]⟩,
    fun v => x ⟨v.val,by simp [Finset.mem_compl.mp v.property]⟩)
  invFun x v := if h : v.val ∈ V then x.1 ⟨v.val,h⟩
    else x.2 ⟨v.val,Finset.mem_compl.mpr (fun hw =>
      (Finset.mem_compl.mp v.property) (Finset.mem_sdiff.mpr ⟨hw,h⟩))⟩
  left_inv x := by funext v; by_cases h : v.val ∈ V <;> simp [h]
  right_inv x := by
    apply Prod.ext
    · funext v; simp [v.property]
    · funext v; simp [show v.val ∉ V from fun h => (Finset.mem_compl.mp v.property) (hVW h)]

def selectedStockRest {I : Inventory} (S : Schedule I)
    (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    (Recorder.Inputs S × Registers S (W \ V)ᶜ) ≃ Record S A V × Record S Aᶜ Wᶜ :=
  (Equiv.prodCongr (registerPartition S A) (relativePartnerPartition S V W hVW)).trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem selected_stock_route {I : Inventory} (S : Schedule I)
    (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    (stockOutputPartition S (W \ V)).trans
      (Equiv.prodCongr (Equiv.refl _) (selectedStockRest S A V W hVW)) =
      ((stockPartition S A W).trans
        (Equiv.prodCongr (outputRefinement S A V W hVW) (Equiv.refl _))).trans
          (Equiv.prodAssoc _ _ _) := by
  apply Equiv.ext
  intro x
  rfl

/-- Flat newly released partners are independent of any retained old record.
All freshness and locality premises have already been derived from the run. -/
theorem fresh_selected_record {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (K : Cut S) (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W)
    (hact : W \ V ⊆ activeVisits S K) :
    withNewOutputsFirst S A V W hVW (chi t (K.val+1) A W) =
      ((outputDimension S (W \ V) : ℂ)⁻¹ • (1 : Mat (Registers S (W \ V)))) ⊗ₖ
        chi t (K.val+1) A V := by
  let ρ := partialRight (rawState t (K.val+1))
  let F := ((stockPartition S A W).trans
    (Equiv.prodCongr (outputRefinement S A V W hVW) (Equiv.refl _)))
  let B := partialRight ((completeRestRecord S t K (W \ V) hact).submatrix
    (selectedStockRest S A V W hVW).symm (selectedStockRest S A V W hVW).symm)
  have hf : withNewOutputsFirst S A V W hVW (chi t (K.val+1) A W) =
      ((outputDimension S (W \ V) : ℂ)⁻¹ • (1 : Mat (Registers S (W \ V)))) ⊗ₖ B := by
    rw [chi_rawMarginal,rawMarginal_body,withNewOutputsFirst,
      ← partialRight_prod_equiv (outputRefinement S A V W hVW).symm (Equiv.refl _)]
    exact tensor_marginal_route (stockOutputPartition S (W \ V)) F
      (selectedStockRest S A V W hVW) (selected_stock_route S A V W hVW) ρ _ _
        (fresh_complete_stock S t K (W \ V) hact)
  have ht : (((outputDimension S (W \ V) : ℂ)⁻¹ • (1 : Mat (Registers S (W \ V))))).trace = 1 := by
    rw [← registers_card]
    simp only [trace_smul,trace_one,smul_eq_mul]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))
  have hb : B = chi t (K.val+1) A V := by
    have h := congrArg partialLeft hf
    rw [partialLeft_kron,ht,one_smul] at h
    rw [chi_rawMarginal,rawMarginal_body] at h
    rw [traceNewOutputs_stock] at h
    simpa only [chi_rawMarginal,rawMarginal_body] using h.symm
  rw [hf,hb]

end History
end ScheduleLaw
