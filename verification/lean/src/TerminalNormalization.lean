import HomogeneousPrefixes

/-! The positive cone in the existing terminal span is exactly the cone
over the normalized feasible terminal histories. No realization premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

theorem terminal_homogeneous_lift {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) : ∃ (a : ℝ) (Z : PrefixMatrices S),
      HomogeneousPrefixEquations S a Z ∧ Z (lastInputBurst S h) = A.val.mat := by
  have aux : ∀ B : HermitianMat (TerminalSpace S h) ℂ, B ∈ terminalSpan S h →
      ∃ (a : ℝ) (Z : PrefixMatrices S),
        HomogeneousPrefixEquations S a Z ∧ Z (lastInputBurst S h) = B.mat := by
    intro B hB
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨Z,hZ,hBZ⟩ := hB
      exact ⟨1,Z,homogeneous_of_causal S Z hZ,hBZ.symm⟩
    | zero => exact ⟨0,0,homogeneous_zero S,rfl⟩
    | add B C hB hC ihB ihC =>
      obtain ⟨a,Z,hZ,hBZ⟩ := ihB
      obtain ⟨b,W,hW,hCW⟩ := ihC
      refine ⟨a+b,Z+W,homogeneous_add S a b Z W hZ hW,?_⟩
      change Z (lastInputBurst S h) + W (lastInputBurst S h) = _
      rw [hBZ,hCW,HermitianMat.mat_add]
    | smul b B hB ihB =>
      obtain ⟨a,Z,hZ,hBZ⟩ := ihB
      refine ⟨b*a,b • Z,homogeneous_smul S a b Z hZ,?_⟩
      change b • Z (lastInputBurst S h) = _
      rw [hBZ,HermitianMat.mat_smul]
  exact aux A.val A.property

def terminalMass {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    terminalSpan S h →ₗ[ℝ] ℝ where
  toFun A := A.val.trace / (prefixDimension (lastInputBurst S h) : ℝ)
  map_add' A B := by
    change (A.val+B.val).trace / _ = _
    rw [HermitianMat.trace_add,add_div]
  map_smul' a A := by
    change (a • A.val).trace / _ = _
    rw [HermitianMat.trace_smul,mul_div_assoc]
    rfl

theorem terminalMass_of_lift {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) (a : ℝ) (Z : PrefixMatrices S)
    (hZ : HomogeneousPrefixEquations S a Z) (hAZ : Z (lastInputBurst S h) = A.val.mat) :
    terminalMass S h A = a := by
  have ht := homogeneous_prefix_trace S a Z hZ (lastInputBurst S h)
  rw [hAZ] at ht
  have hr : A.val.trace = a * (prefixDimension (lastInputBurst S h) : ℝ) := by
    simpa only [HermitianMat.trace,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero] using congrArg Complex.re ht
  change A.val.trace / _ = a
  rw [hr]
  have hc : (prefixDimension (lastInputBurst S h) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (outputDimension_pos S (released S (recordTime (lastInputBurst S h))))
  field_simp

theorem terminalMass_nonneg {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) (hA : 0 ≤ A.val) : 0 ≤ terminalMass S h A :=
  div_nonneg (HermitianMat.trace_nonneg hA) (Nat.cast_nonneg _)

theorem terminalMass_eq_one_of_feasible {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) (hA : A.val ∈ terminalFamilySet S h) : terminalMass S h A = 1 := by
  obtain ⟨Z,hZ,hAZ⟩ := hA
  exact terminalMass_of_lift S h A 1 Z (homogeneous_of_causal S Z hZ) hAZ.symm

theorem terminalMass_flat {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    terminalMass S h (terminalFlatVector S h) = 1 :=
  terminalMass_eq_one_of_feasible S h _ (terminal_flat_mem S h)

theorem terminalMass_tester {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) : terminalMass S h (terminalTesterVector S h t) = 1 :=
  terminalMass_eq_one_of_feasible S h _
    ⟨(fun b => prefixGram b t),actual_causal_prefix_family S t,rfl⟩

theorem terminalMass_zero_positive {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) (hA : 0 ≤ A.val) (hz : terminalMass S h A = 0) : A = 0 := by
  have ht : A.val.trace = 0 := by
    change A.val.trace / (prefixDimension (lastInputBurst S h) : ℝ) = 0 at hz
    exact (div_eq_zero_iff.mp hz).resolve_right
      (by exact_mod_cast ne_of_gt (outputDimension_pos S _))
  apply Subtype.ext
  exact norm_eq_zero.mp (le_antisymm (by simpa only [ht] using positive_norm_le_trace A.val hA)
    (norm_nonneg _))

theorem terminalMass_pos {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) (hA : 0 ≤ A.val) (hne : A ≠ 0) : 0 < terminalMass S h A :=
  lt_of_le_of_ne (terminalMass_nonneg S h A hA)
    (fun he => hne (terminalMass_zero_positive S h A hA he.symm))

theorem positive_terminal_normalize {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) (hA : 0 ≤ A.val) (hne : A ≠ 0) :
    (terminalMass S h A)⁻¹ • A.val ∈ terminalFamilySet S h := by
  obtain ⟨a,Z,hZ,hAZ⟩ := terminal_homogeneous_lift S h A
  have hm := terminalMass_of_lift S h A a Z hZ hAZ
  have ha : 0 < a := hm ▸ terminalMass_pos S h A hA hne
  have hp : (Z (lastInputBurst S h)).PosSemidef := by
    rw [hAZ]
    exact HermitianMat.zero_le_iff.mp hA
  refine ⟨a⁻¹ • Z,homogeneous_normalize S h a ha Z hZ hp,?_⟩
  rw [HermitianMat.mat_smul,hm]
  change a⁻¹ • A.val.mat = a⁻¹ • Z (lastInputBurst S h)
  rw [hAZ]

theorem terminal_cone_normalization {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) : 0 ≤ A.val ↔ A = 0 ∨
      ∃ (a : ℝ) (B : HermitianMat (TerminalSpace S h) ℂ),
        0 < a ∧ B ∈ terminalFamilySet S h ∧ A.val = a • B := by
  constructor
  · intro hA
    by_cases hz : A = 0
    · exact Or.inl hz
    · refine Or.inr ⟨terminalMass S h A,(terminalMass S h A)⁻¹ • A.val,
        terminalMass_pos S h A hA hz,positive_terminal_normalize S h A hA hz,?_⟩
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (terminalMass_pos S h A hA hz)),one_smul]
  · rintro (rfl | ⟨a,B,ha,⟨Z,hZ,hBZ⟩,hAB⟩)
    · exact le_rfl
    · rw [hAB]
      apply smul_nonneg ha.le
      apply HermitianMat.zero_le_iff.mpr
      rw [hBZ]
      exact hZ.1 _

end ScheduleLaw.History
