import PureFactor

/-! Exact tensor splitting of normalized EPR stock under visit partitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

instance registersNonempty {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Nonempty (Registers S V) := ⟨fun v => ⟨0,I.dim_pos (S.carrier v.val)⟩⟩

theorem epr_equiv {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (x : a × a) : Recorder.epr (e x.1,e x.2) = Recorder.epr x := by
  unfold Recorder.epr
  rw [← Fintype.card_congr e]
  simp only [e.injective.eq_iff]

theorem epr_product {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (x y : a × b) : Recorder.epr (x,y) = Recorder.epr (x.1,y.1) * Recorder.epr (x.2,y.2) := by
  simp only [Recorder.epr,Fintype.card_prod,Prod.ext_iff,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _),mul_inv,Complex.ofReal_mul]
  split_ifs <;> simp_all

theorem stock_epr_split {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits))
    (x : Record S V V × Record S Vᶜ Vᶜ) :
    Recorder.epr ((stockPartition S V V).symm x) = Recorder.epr x.1 * Recorder.epr x.2 := by
  rw [← epr_equiv (registerPartition S V) ((stockPartition S V V).symm x)]
  have he : (stockPartition S V V).symm x =
      ((registerPartition S V).symm (x.1.1,x.2.1),(registerPartition S V).symm (x.1.2,x.2.2)) := rfl
  rw [he]
  simp only [Equiv.apply_symm_apply]
  exact epr_product _ _

theorem pure_stock_epr_split {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    (pureMatrix (Recorder.epr (a := Recorder.Inputs S))).submatrix
      (stockPartition S V V).symm (stockPartition S V V).symm =
      pureMatrix (Recorder.epr (a := Registers S V)) ⊗ₖ
        pureMatrix (Recorder.epr (a := Registers S Vᶜ)) := by
  ext i j
  simp only [submatrix_apply,pureMatrix,stock_epr_split,kroneckerMap_apply,star_mul]
  ring

theorem subset_epr_trace {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    (pureMatrix (Recorder.epr (a := Registers S V))).trace = 1 := by
  rw [pureMatrix_trace,Recorder.epr_normalized,Complex.ofReal_one]

theorem initial_pair_marginal {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r)
    (V : Finset (Fin S.visits)) :
    rawMarginal S r V V ((run (Recorder.extension S) t 0).submatrix (actual S r) (actual S r)) =
      pureMatrix (Recorder.epr (a := Registers S V)) := by
  rw [← chi_rawMarginal,chi_as_body]
  rw [run,initial_body_reduction]
  change partialRight (((Recorder.source S).matrix.submatrix (Recorder.stockFin S)
    (Recorder.stockFin S)).submatrix (stockPartition S V V).symm (stockPartition S V V).symm) = _
  rw [Recorder.source_exact,pure_stock_epr_split,partialRight_kron,subset_epr_trace,one_smul]

end History
end ScheduleLaw
