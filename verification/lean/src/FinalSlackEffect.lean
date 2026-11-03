import BlueprintJointTangent

/-! The physical slack representative remains available in the retained body
at the terminal cut, uniformly over coherent testers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

theorem rareHistoryEffect_final {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (D : HermitianMat (TerminalSpace S h) ℂ) {r : ℕ} (t : Tester S r) :
    energy (rareHistoryEffect e h δ hδ.le hδ1 D)
      (bodyOutput (Recorder.rare e δ hδ.le hδ1) t) =
        inner ℝ D (terminalTesterVector S h t : HermitianMat (TerminalSpace S h) ℂ) := by
  unfold bodyOutput finalState
  rw [rareHistoryEffect_expectation e h δ hδ hδ1 D t]
  exact recorderHistoryEffect_expectation S h t D

theorem physical_slack_effect_final {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : Density (Fin (Recorder.rare e δ hδ.le hδ1).b)) (hq : q.matrix.PosDef) (w a : ℝ)
    (hmax : ∀ r (t : Tester S r), physicalLinearized β (Recorder.rare e δ hδ.le hδ1) q t ≤ w)
    (hup : sourceFreeTerm β (Recorder.rare e δ hδ.le hδ1) q+w ≤
      scoreBound β (Recorder.rare e δ hδ.le hδ1)+a) :
    ∃ D : Mat (Fin (Recorder.rare e δ hδ.le hδ1).b), D.PosSemidef ∧
      ‖D‖ ≤ (prefixDimension (lastInputBurst S h) : ℝ)*(terminalInputDimension S h : ℝ)*
        (2*scoreBound β (Recorder.rare e δ hδ.le hδ1)+a)/δ ∧
      ∀ r (t : Tester S r), energy D (bodyOutput (Recorder.rare e δ hδ.le hδ1) t) = w-physicalLinearized β (Recorder.rare e δ hδ.le hδ1) q t := by
  let er := Recorder.rare e δ hδ.le hδ1
  obtain ⟨J,hJ⟩ := physical_J_terminal β er q h
  have hb : ∀ A : terminalSpan S h, A.val ∈ terminalFamilySet S h → J A ≤ w := by
    intro A hA
    rw [← terminalTesterSet_eq eliminate_comb S h] at hA
    obtain ⟨r,t,ht⟩ := hA
    have he : A=terminalTesterVector S h t := Subtype.ext (HermitianMat.ext ht)
    rw [he,hJ]
    exact hmax r t
  have hf : (terminalFlatVector S h).val ∈ terminalFamilySet S h := terminal_flat_mem S h
  rw [← terminalTesterSet_eq eliminate_comb S h] at hf
  obtain ⟨r0,t0,ht0⟩ := hf
  have hflat : terminalFlatVector S h=terminalTesterVector S h t0 :=
    Subtype.ext (HermitianMat.ext ht0)
  have hfb : w-J (terminalFlatVector S h) ≤ 2*scoreBound β er+a := by
    rw [hflat,hJ]
    exact physical_flat_slack_estimate β hβ er q hq w a hup t0
  obtain ⟨D,hD,hn,he⟩ := rare_slack_history_effect e h δ hδ hδ1 J w hb
  refine ⟨rareHistoryEffect e h δ hδ.le hδ1 D,hD,?_,?_⟩
  · calc ‖rareHistoryEffect e h δ hδ.le hδ1 D‖ ≤ δ⁻¹ *
          ((prefixDimension (lastInputBurst S h) : ℝ)*(terminalInputDimension S h : ℝ)*
            (w-J (terminalFlatVector S h))) := hn
      _ ≤ δ⁻¹ * ((prefixDimension (lastInputBurst S h) : ℝ)*(terminalInputDimension S h : ℝ)*
          (2*scoreBound β er+a)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfb (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          (inv_nonneg.mpr hδ.le)
      _ = _ := by ring
  · intro r t
    rw [rareHistoryEffect_final e h δ hδ hδ1 D t,
      ← rareHistoryEffect_at_record e h δ hδ hδ1 D t,he,hJ]

end ScheduleLaw.Blueprint
