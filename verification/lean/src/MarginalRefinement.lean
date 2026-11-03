import StockDecoupling

/-! Exact successive partial traces under visit-subset refinement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def complementRefinement {I : Inventory} (S : Schedule I)
    (V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Registers S Vᶜ ≃ Registers S (W \ V) × Registers S Wᶜ where
  toFun x := (fun v => x ⟨v.val,Finset.mem_compl.mpr (Finset.mem_sdiff.mp v.property).2⟩,
    fun v => x ⟨v.val,Finset.mem_compl.mpr (fun h => (Finset.mem_compl.mp v.property) (hVW h))⟩)
  invFun x v := if h : v.val ∈ W then
    x.1 ⟨v.val,Finset.mem_sdiff.mpr ⟨h,Finset.mem_compl.mp v.property⟩⟩
    else x.2 ⟨v.val,Finset.mem_compl.mpr h⟩
  left_inv x := by funext v; by_cases h : v.val ∈ W <;> simp [h]
  right_inv x := by
    apply Prod.ext
    · funext v; simp [(Finset.mem_sdiff.mp v.property).1]
    · funext v; simp [Finset.mem_compl.mp v.property]

def inputEnvironmentRefinement {I : Inventory} (S : Schedule I)
    (V W O : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Record S Vᶜ Oᶜ ≃ Registers S (W \ V) × Record S Wᶜ Oᶜ :=
  (Equiv.prodCongr (complementRefinement S V W hVW) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

theorem input_refinement_route {I : Inventory} (S : Schedule I)
    (V W O : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    (stockPartition S V O).trans (Equiv.prodCongr (Equiv.refl _)
      (inputEnvironmentRefinement S V W O hVW)) =
      ((stockPartition S W O).trans
        (Equiv.prodCongr (inputRefinement S V W O hVW) (Equiv.refl _))).trans
          (Equiv.prodAssoc _ _ _) := by
  apply Equiv.ext
  intro x
  rfl

theorem nested_partial_trace {x a b z w : Type} [Fintype b] [Fintype z] [Fintype w]
    (coarse : x ≃ a × z) (fine : x ≃ (a × b) × w) (env : z ≃ b × w)
    (hr : coarse.trans (Equiv.prodCongr (Equiv.refl _) env) =
      fine.trans (Equiv.prodAssoc _ _ _)) (ρ : Mat x) :
    partialRight (partialRight (ρ.submatrix fine.symm fine.symm)) =
      partialRight (ρ.submatrix coarse.symm coarse.symm) := by
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
  simp only [partialRight,submatrix_apply,he]
  exact (Fintype.sum_prod_type _).symm.trans
    (Equiv.sum_comp env.symm (fun k => ρ (coarse.symm (i,k)) (coarse.symm (j,k))))

theorem traceNewInputs_stock {I : Inventory} (S : Schedule I)
    (V W O : Finset (Fin S.visits)) (hVW : V ⊆ W) (ρ : Mat (Recorder.Stock S)) :
    traceNewInputs S V W O hVW
      (partialRight (ρ.submatrix (stockPartition S W O).symm (stockPartition S W O).symm)) =
    partialRight (ρ.submatrix (stockPartition S V O).symm (stockPartition S V O).symm) := by
  have h := nested_partial_trace (stockPartition S V O)
    ((stockPartition S W O).trans
      (Equiv.prodCongr (inputRefinement S V W O hVW) (Equiv.refl _)))
    (inputEnvironmentRefinement S V W O hVW) (input_refinement_route S V W O hVW) ρ
  rw [traceNewInputs]
  rw [← partialRight_prod_equiv (inputRefinement S V W O hVW).symm (Equiv.refl _)]
  exact h

theorem traceNewInputs_chi {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (n : ℕ) (V W O : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    traceNewInputs S V W O hVW (chi t n W O) = chi t n V O := by
  simp only [chi_rawMarginal,rawMarginal_body]
  exact traceNewInputs_stock S V W O hVW _

end History
end ScheduleLaw
