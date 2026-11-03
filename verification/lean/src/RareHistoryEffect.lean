import TerminalSlack
import RecorderPerturbation

/-! Exact rare-flag amplification of the actual retained history effect.
The expectation identity holds at every run time, and the operator norm
has precisely the inverse rare-probability factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.History

def blockRightHom (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Mat b →⋆ₙₐ[ℂ] Mat (a ⊕ b) where
  toFun B := ClassicalFlag.block 0 B
  map_zero' := by ext i j; cases i <;> cases j <;> simp [ClassicalFlag.block]
  map_add' B C := by ext i j; cases i <;> cases j <;> simp [ClassicalFlag.block]
  map_mul' B C := by simp [ClassicalFlag.block,fromBlocks_multiply]
  map_smul' c B := by ext i j; cases i <;> cases j <;> simp [ClassicalFlag.block]
  map_star' B := by
    change ClassicalFlag.block 0 Bᴴ = (ClassicalFlag.block (0 : Mat a) B)ᴴ
    simp [ClassicalFlag.block,fromBlocks_conjTranspose]

theorem blockRightHom_injective {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] : Function.Injective (blockRightHom a b) := by
  intro B C he
  ext i j
  exact congrFun₂ he (Sum.inr i) (Sum.inr j)

theorem zero_block_opNorm {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (B : Mat b) :
    ‖ClassicalFlag.block (0 : Mat a) B‖ = ‖B‖ := by
  letI := matrixCStarStructure b
  letI := matrixCStarStructure (a ⊕ b)
  exact NonUnitalStarAlgHom.norm_map (blockRightHom a b) blockRightHom_injective B

theorem zero_block_positive {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (B : Mat b) (hB : B.PosSemidef) :
    (ClassicalFlag.block (0 : Mat a) B).PosSemidef := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨ClassicalFlag.block_hermitian 0 B (by simp) hB.isHermitian,?_⟩
  intro x
  simpa [ClassicalFlag.block,Matrix.mulVec,dotProduct,Fintype.sum_sum_type] using
    (posSemidef_iff_dotProduct_mulVec.mp hB).2 (x ∘ Sum.inr)

theorem energy_blocks {a b : Type} [Fintype a] [Fintype b]
    (H A : Mat a) (K B : Mat b) :
    energy (ClassicalFlag.block H K) (ClassicalFlag.block A B) = energy H A + energy K B := by
  simp [energy,ClassicalFlag.block,fromBlocks_multiply,ClassicalFlag.block_trace,trace,
    Fintype.sum_sum_type]

theorem energy_observable_weight {a : Type} [Fintype a] (H ρ : Mat a) (c : ℝ) :
    energy ((c : ℂ) • H) ρ = c * energy H ρ := by
  simp [energy,smul_mul_assoc,trace_smul]

def rareHistoryEffect {I : Inventory} {S : Schedule I} (e : Extension S) (h : 0 < S.visits)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (D : HermitianMat (TerminalSpace S h) ℂ) :
    Mat (Fin (Recorder.rare e δ hδ hδ1).b) :=
  (ClassicalFlag.block (0 : Mat (Fin (IdleExtension.extension e (Recorder.flatStock S)).b))
    (((((δ⁻¹ : ℝ) : ℂ) • recorderHistoryEffect S h D) ⊗ₖ (1 : Mat (Fin e.b))).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm

theorem rareHistoryEffect_norm {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (D : HermitianMat (TerminalSpace S h) ℂ) :
    ‖rareHistoryEffect e h δ hδ.le hδ1 D‖ = δ⁻¹ * ‖recorderHistoryEffect S h D‖ := by
  letI : Nonempty (Fin e.b) := ⟨⟨0,e.b_pos⟩⟩
  unfold rareHistoryEffect
  rw [reindex_opNorm (finSumFinEquiv.symm :
    Fin ((IdleExtension.extension e (Recorder.flatStock S)).b + (IdleExtension.extension (Recorder.extension S) e).b) ≃
      Fin (IdleExtension.extension e (Recorder.flatStock S)).b ⊕ Fin (IdleExtension.extension (Recorder.extension S) e).b),
    zero_block_opNorm,reindex_opNorm (finProdFinEquiv.symm :
      Fin ((Recorder.extension S).b * e.b) ≃ Fin (Recorder.extension S).b × Fin e.b),
    kron_identity_opNorm,norm_smul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hδ.le)]

theorem rareHistoryEffect_positive {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (D : HermitianMat (TerminalSpace S h) ℂ)
    (hD : (recorderHistoryEffect S h D).PosSemidef) :
    (rareHistoryEffect e h δ hδ.le hδ1 D).PosSemidef := by
  apply Matrix.PosSemidef.submatrix
  apply zero_block_positive
  apply Matrix.PosSemidef.submatrix
  exact (hD.smul (show (0 : ℂ) ≤ ((δ⁻¹ : ℝ) : ℂ) by
    exact_mod_cast inv_nonneg.mpr hδ.le)).kronecker Matrix.PosSemidef.one

theorem rareHistoryEffect_expectation {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (D : HermitianMat (TerminalSpace S h) ℂ) {r : ℕ} (t : Tester S r) (n : ℕ) :
    energy (rareHistoryEffect e h δ hδ.le hδ1 D)
      (partialRight (run (Recorder.rare e δ hδ.le hδ1) t n)) =
        energy (recorderHistoryEffect S h D) (partialRight (run (Recorder.extension S) t n)) := by
  have hb : partialRight (run (IdleExtension.extension (Recorder.extension S) e) t n) =
      (partialRight (run (Recorder.extension S) t n) ⊗ₖ e.source.matrix).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
    rw [IdleExtension.run_idle]
    exact IdleExtension.partialRight_idle _ e.source.matrix
  unfold Recorder.rare
  rw [ClassicalFlag.run_branches,ClassicalFlag.partialRight_branches,
    ClassicalFlag.partialRight_weight,ClassicalFlag.partialRight_weight]
  unfold rareHistoryEffect
  rw [energy_reindex (finSumFinEquiv.symm :
    Fin ((IdleExtension.extension e (Recorder.flatStock S)).b + (IdleExtension.extension (Recorder.extension S) e).b) ≃
      Fin (IdleExtension.extension e (Recorder.flatStock S)).b ⊕ Fin (IdleExtension.extension (Recorder.extension S) e).b),
    energy_blocks]
  simp only [energy,Matrix.zero_mul,trace_zero,Complex.zero_re,zero_add]
  change energy _ ((δ : ℂ) • partialRight (run (IdleExtension.extension (Recorder.extension S) e) t n)) = _
  rw [ClassicalFlag.energy_weight,hb,
    energy_reindex (finProdFinEquiv.symm : Fin ((Recorder.extension S).b * e.b) ≃
      Fin (Recorder.extension S).b × Fin e.b),energy_kron_one,partialRight_kron,e.source.normalized,one_smul,
    energy_observable_weight]
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hδ),one_mul]
  rfl

theorem rareHistoryEffect_at_record {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (D : HermitianMat (TerminalSpace S h) ℂ) {r : ℕ} (t : Tester S r) :
    energy (rareHistoryEffect e h δ hδ.le hδ1 D)
      (partialRight (run (Recorder.rare e δ hδ.le hδ1) t (recordTime (lastInputBurst S h)))) =
        inner ℝ D (terminalTesterVector S h t : HermitianMat (TerminalSpace S h) ℂ) := by
  rw [rareHistoryEffect_expectation e h δ hδ hδ1 D t _,recorderHistoryEffect_at_record]

theorem rare_slack_history_effect {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (J : terminalSpan S h →ₗ[ℝ] ℝ) (w : ℝ)
    (hmax : ∀ A : terminalSpan S h, A.val ∈ terminalFamilySet S h → J A ≤ w) :
    ∃ D : HermitianMat (TerminalSpace S h) ℂ,
      (rareHistoryEffect e h δ hδ.le hδ1 D).PosSemidef ∧
      ‖rareHistoryEffect e h δ hδ.le hδ1 D‖ ≤ δ⁻¹ *
        ((prefixDimension (lastInputBurst S h) : ℝ) * (terminalInputDimension S h : ℝ) *
          (w-J (terminalFlatVector S h))) ∧
      ∀ r (t : Tester S r), energy (rareHistoryEffect e h δ hδ.le hδ1 D)
        (partialRight (run (Recorder.rare e δ hδ.le hδ1) t (recordTime (lastInputBurst S h)))) =
          w-J (terminalTesterVector S h t) := by
  obtain ⟨D,hD,hn,he⟩ := terminal_slack_history_effect S h J w hmax
  refine ⟨D,rareHistoryEffect_positive e h δ hδ hδ1 D hD,?_,?_⟩
  · rw [rareHistoryEffect_norm e h δ hδ hδ1 D]
    exact mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hδ.le)
  · intro r t
    rw [rareHistoryEffect_expectation e h δ hδ hδ1 D t _]
    exact he r t

end ScheduleLaw.History
