import RecorderGram

/-! Explicit tensor coordinates for nested visit-register sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def registersCongr {I : Inventory} (S : Schedule I) {V W : Finset (Fin S.visits)} (h : V = W) :
    Registers S V ≃ Registers S W := by subst W; exact Equiv.refl _

def registerRefinement {I : Inventory} (S : Schedule I) (V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Registers S W ≃ Registers S V × Registers S (W \ V) where
  toFun a := (fun v => a ⟨v.val,hVW v.property⟩,
    fun v => a ⟨v.val,(Finset.mem_sdiff.mp v.property).1⟩)
  invFun a v := if h : v.val ∈ V then a.1 ⟨v.val,h⟩
    else a.2 ⟨v.val,Finset.mem_sdiff.mpr ⟨v.property,h⟩⟩
  left_inv a := by funext v; by_cases h : v.val ∈ V <;> simp [h]
  right_inv a := by
    apply Prod.ext
    · funext v; simp [v.property]
    · funext v; simp [(Finset.mem_sdiff.mp v.property).2]

theorem registerRefinement_old {I : Inventory} (S : Schedule I) (V W : Finset (Fin S.visits))
    (hVW : V ⊆ W) (a : Registers S W) (v : {v // v ∈ V}) :
    (registerRefinement S V W hVW a).1 v = a ⟨v.val,hVW v.property⟩ := rfl

theorem registerRefinement_new {I : Inventory} (S : Schedule I) (V W : Finset (Fin S.visits))
    (hVW : V ⊆ W) (a : Registers S W) (v : {v // v ∈ W \ V}) :
    (registerRefinement S V W hVW a).2 v = a ⟨v.val,(Finset.mem_sdiff.mp v.property).1⟩ := rfl

theorem registers_card {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Fintype.card (Registers S V) = outputDimension S V := by
  simp only [Registers,Fintype.card_pi,Fintype.card_fin,outputDimension]
  exact Finset.prod_coe_sort V (fun v => I.dim (S.carrier v))

theorem outputDimension_refinement {I : Inventory} (S : Schedule I)
    (V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    outputDimension S W = outputDimension S V * outputDimension S (W \ V) := by
  have hc := Fintype.card_congr (registerRefinement S V W hVW)
  simpa only [Fintype.card_prod,registers_card] using hc

def inputRefinement {I : Inventory} (S : Schedule I) (V W O : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Record S W O ≃ Record S V O × Registers S (W \ V) where
  toFun x := (((registerRefinement S V W hVW x.1).1,x.2),(registerRefinement S V W hVW x.1).2)
  invFun x := ((registerRefinement S V W hVW).symm (x.1.1,x.2),x.1.2)
  left_inv x := by
    change ((registerRefinement S V W hVW).symm (registerRefinement S V W hVW x.1),x.2) = x
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    have he := (registerRefinement S V W hVW).apply_symm_apply (x.1.1,x.2)
    change (((registerRefinement S V W hVW ((registerRefinement S V W hVW).symm (x.1.1,x.2))).1,x.1.2),
      (registerRefinement S V W hVW ((registerRefinement S V W hVW).symm (x.1.1,x.2))).2) = x
    rw [he]

/-- New output partners occur first in this coordinate convention, so the
causal equation has the requested identity tensor previous-prefix order. -/
def outputRefinement {I : Inventory} (S : Schedule I) (A V W : Finset (Fin S.visits)) (hVW : V ⊆ W) :
    Record S A W ≃ Registers S (W \ V) × Record S A V where
  toFun x := ((registerRefinement S V W hVW x.2).2,(x.1,(registerRefinement S V W hVW x.2).1))
  invFun x := (x.2.1,(registerRefinement S V W hVW).symm (x.2.2,x.1))
  left_inv x := by
    change (x.1,(registerRefinement S V W hVW).symm (registerRefinement S V W hVW x.2)) = x
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    have he := (registerRefinement S V W hVW).apply_symm_apply (x.2.2,x.1)
    change ((registerRefinement S V W hVW ((registerRefinement S V W hVW).symm (x.2.2,x.1))).2,
      (x.2.1,(registerRefinement S V W hVW ((registerRefinement S V W hVW).symm (x.2.2,x.1))).1)) = x
    rw [he]

def traceNewInputs {I : Inventory} (S : Schedule I) (V W O : Finset (Fin S.visits))
    (hVW : V ⊆ W) (ρ : Mat (Record S W O)) : Mat (Record S V O) :=
  partialRight (ρ.submatrix (inputRefinement S V W O hVW).symm (inputRefinement S V W O hVW).symm)

def withNewOutputsFirst {I : Inventory} (S : Schedule I) (A V W : Finset (Fin S.visits))
    (hVW : V ⊆ W) (ρ : Mat (Record S A W)) : Mat (Registers S (W \ V) × Record S A V) :=
  ρ.submatrix (outputRefinement S A V W hVW).symm (outputRefinement S A V W hVW).symm

theorem traceNewInputs_weight {I : Inventory} (S : Schedule I) (V W O : Finset (Fin S.visits))
    (hVW : V ⊆ W) (ρ : Mat (Record S W O)) (c : ℂ) :
    traceNewInputs S V W O hVW (c • ρ) = c • traceNewInputs S V W O hVW ρ := by
  unfold traceNewInputs
  exact ClassicalFlag.partialRight_weight _ c

theorem withNewOutputsFirst_weight {I : Inventory} (S : Schedule I) (A V W : Finset (Fin S.visits))
    (hVW : V ⊆ W) (ρ : Mat (Record S A W)) (c : ℂ) :
    withNewOutputsFirst S A V W hVW (c • ρ) = c • withNewOutputsFirst S A V W hVW ρ := rfl

end History
end ScheduleLaw
