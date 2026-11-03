import TerminalNormalization

/-! Positive slack for a linear terminal-history functional. Its positivity
is derived from its bound on normalized feasible histories. This module does
not assume an operational body/energy factorization for any extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.History

def terminalSlack {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (J : terminalSpan S h →ₗ[ℝ] ℝ) (w : ℝ) : terminalSpan S h →ₗ[ℝ] ℝ :=
  w • terminalMass S h - J

theorem terminalSlack_nonneg {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (J : terminalSpan S h →ₗ[ℝ] ℝ) (w : ℝ)
    (hmax : ∀ A : terminalSpan S h, A.val ∈ terminalFamilySet S h → J A ≤ w)
    (A : terminalSpan S h) (hA : 0 ≤ A.val) : 0 ≤ terminalSlack S h J w A := by
  by_cases hz : A = 0
  · subst A; simp
  have hm := terminalMass_pos S h A hA hz
  let B : terminalSpan S h := (terminalMass S h A)⁻¹ • A
  have hB : B.val ∈ terminalFamilySet S h := positive_terminal_normalize S h A hA hz
  have hrec : terminalMass S h A • B = A := by
    dsimp only [B]
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hm),one_smul]
  have hbound : J A ≤ terminalMass S h A * w := by
    calc J A = J (terminalMass S h A • B) := congrArg J hrec.symm
      _ = terminalMass S h A * J B := J.map_smul _ _
      _ ≤ terminalMass S h A * w := mul_le_mul_of_nonneg_left (hmax B hB) hm.le
  change 0 ≤ w * terminalMass S h A - J A
  linarith

theorem terminalSlack_flat {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (J : terminalSpan S h →ₗ[ℝ] ℝ) (w : ℝ) :
    terminalSlack S h J w (terminalFlatVector S h) = w - J (terminalFlatVector S h) := by
  change w * terminalMass S h (terminalFlatVector S h) - _ = _
  rw [terminalMass_flat,mul_one]

theorem terminalSlack_tester {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (J : terminalSpan S h →ₗ[ℝ] ℝ) (w : ℝ) {r : ℕ} (t : Tester S r) :
    terminalSlack S h J w (terminalTesterVector S h t) = w - J (terminalTesterVector S h t) := by
  change w * terminalMass S h (terminalTesterVector S h t) - _ = _
  rw [terminalMass_tester,mul_one]

theorem terminal_slack_history_effect {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (J : terminalSpan S h →ₗ[ℝ] ℝ) (w : ℝ)
    (hmax : ∀ A : terminalSpan S h, A.val ∈ terminalFamilySet S h → J A ≤ w) :
    ∃ D : HermitianMat (TerminalSpace S h) ℂ,
      (recorderHistoryEffect S h D).PosSemidef ∧
      ‖recorderHistoryEffect S h D‖ ≤ (prefixDimension (lastInputBurst S h) : ℝ) *
        (terminalInputDimension S h : ℝ) * (w - J (terminalFlatVector S h)) ∧
      ∀ r (t : Tester S r), energy (recorderHistoryEffect S h D)
        (partialRight (run (Recorder.extension S) t (recordTime (lastInputBurst S h)))) =
          w - J (terminalTesterVector S h t) := by
  obtain ⟨D,hD,hn,he⟩ := positive_accessible_history_effect S h (terminalSlack S h J w)
    (terminalSlack_nonneg S h J w hmax)
  rw [terminalSlack_flat] at hn
  exact ⟨D,hD,hn,fun r t => (he r t).trans (terminalSlack_tester S h J w t)⟩

theorem flat_slack_bound {F w j C a : ℝ} (hup : F+w ≤ C+a) (hlo : -C ≤ F+j) :
    w-j ≤ 2*C+a := by linarith

end ScheduleLaw.History
