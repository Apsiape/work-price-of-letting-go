import TerminalGeometry

/-! A positive history representative is an actual positive observable on
the Recorder's retained finite body. Its expectation is the same linear
functional, and its bound uses the operator norm in the circuit convention. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
  InnerProductSpace RealInnerProductSpace
namespace ScheduleLaw.History

theorem positive_opNorm_le_trace {a : Type} [Fintype a] [DecidableEq a]
    (D : HermitianMat a ℂ) (hD : 0 ≤ D) : ‖D.mat‖ ≤ D.trace := by
  let U := D.H.eigenvectorUnitary
  rw [D.H.spectral_theorem]
  change ‖(U : Mat a) * diagonal (fun i => (D.H.eigenvalues i : ℂ)) * (↑(star U) : Mat a)‖ ≤ _
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (HermitianMat.trace_nonneg hD)).mpr
  intro i
  have hn := (HermitianMat.zero_le_iff.mp hD).eigenvalues_nonneg i
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  rw [← HermitianMat.sum_eigenvalues_eq_trace D]
  exact Finset.single_le_sum (fun j _ => (HermitianMat.zero_le_iff.mp hD).eigenvalues_nonneg j)
    (Finset.mem_univ i)

def recorderHistoryEffect {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (D : HermitianMat (TerminalSpace S h) ℂ) : Mat (Fin (Recorder.extension S).b) :=
  let b := lastInputBurst S h
  let p := stockPartition S (arrived S (recordTime b)) (released S (recordTime b))
  (((prefixDimension b : ℂ) • D.mat) ⊗ₖ (1 : Mat (Record S
    (arrived S (recordTime b))ᶜ (released S (recordTime b))ᶜ))).submatrix
      ((Recorder.stockFin S).symm.trans p) ((Recorder.stockFin S).symm.trans p)

theorem recorderHistoryEffect_positive {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (D : HermitianMat (TerminalSpace S h) ℂ) (hD : 0 ≤ D) :
    (recorderHistoryEffect S h D).PosSemidef := by
  apply Matrix.PosSemidef.submatrix
  apply Matrix.PosSemidef.kronecker _ Matrix.PosSemidef.one
  exact (HermitianMat.zero_le_iff.mp hD).smul
    (show (0 : ℂ) ≤ (prefixDimension (lastInputBurst S h) : ℂ) by
      exact_mod_cast le_of_lt (outputDimension_pos S _))

theorem recorderHistoryEffect_expectation {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) (D : HermitianMat (TerminalSpace S h) ℂ) :
    energy (recorderHistoryEffect S h D) (bodyOutput (Recorder.extension S) t) =
      ⟪D,(terminalTesterVector S h t : HermitianMat (TerminalSpace S h) ℂ)⟫_ℝ := by
  let b := lastInputBurst S h
  let p := stockPartition S (arrived S (recordTime b)) (released S (recordTime b))
  have hp : chi t (2*S.visits+1) (arrived S (recordTime b)) (released S (recordTime b)) =
      partialRight ((bodyOutput (Recorder.extension S) t).submatrix
        (p.symm.trans (Recorder.stockFin S)) (p.symm.trans (Recorder.stockFin S))) :=
    chi_as_body t _ _ _
  have he : energy (recorderHistoryEffect S h D) (bodyOutput (Recorder.extension S) t) =
      energy ((prefixDimension b : ℂ) • D.mat)
        (chi t (2*S.visits+1) (arrived S (recordTime b)) (released S (recordTime b))) := by
    rw [hp]
    rw [← energy_kron_one]
    have hr : (recorderHistoryEffect S h D).submatrix
        (p.symm.trans (Recorder.stockFin S)) (p.symm.trans (Recorder.stockFin S)) =
        ((prefixDimension b : ℂ) • D.mat) ⊗ₖ
          (1 : Mat (Record S (arrived S (recordTime b))ᶜ (released S (recordTime b))ᶜ)) := by
      ext i j
      simp only [recorderHistoryEffect,submatrix_apply,Equiv.trans_apply,
        Equiv.symm_apply_apply,Equiv.apply_symm_apply,p,b]
    have ht := energy_reindex (p.symm.trans (Recorder.stockFin S))
      (recorderHistoryEffect S h D) (bodyOutput (Recorder.extension S) t)
    exact ht.symm.trans (congrArg
      (fun M => energy M ((bodyOutput (Recorder.extension S) t).submatrix
        (p.symm.trans (Recorder.stockFin S)) (p.symm.trans (Recorder.stockFin S)))) hr)
  rw [he,terminal_recorder_identity S h t]
  unfold energy
  rw [smul_mul_smul,mul_inv_cancel₀
    (by exact_mod_cast ne_of_gt (outputDimension_pos S (released S (recordTime b)))),one_smul]
  simpa only [terminalTesterVector] using
    (HermitianMat.inner_eq_re_trace D
      (terminalTesterVector S h t : HermitianMat (TerminalSpace S h) ℂ)).symm

theorem positive_recorder_representative {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (L : terminalSpan S h →ₗ[ℝ] ℝ)
    (hL : ∀ A : terminalSpan S h, 0 ≤ (A : HermitianMat (TerminalSpace S h) ℂ) → 0 ≤ L A) :
    ∃ D : HermitianMat (TerminalSpace S h) ℂ, 0 ≤ D ∧
      ‖D.mat‖ ≤ (terminalInputDimension S h : ℝ) * L (terminalFlatVector S h) ∧
      (recorderHistoryEffect S h D).PosSemidef ∧
      ∀ r (t : Tester S r),
        energy (recorderHistoryEffect S h D) (bodyOutput (Recorder.extension S) t) =
          L (terminalTesterVector S h t) := by
  obtain ⟨D,hD,hev,ht,hn⟩ := terminal_positive_representative S h L hL
  refine ⟨D,hD,(positive_opNorm_le_trace D hD).trans_eq ht,
    recorderHistoryEffect_positive S h D hD,?_⟩
  intro r t
  rw [recorderHistoryEffect_expectation]
  exact hev (terminalTesterVector S h t)

end ScheduleLaw.History
