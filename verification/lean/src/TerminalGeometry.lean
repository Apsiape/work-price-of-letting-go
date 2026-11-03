import ProjectedPSD
import PrefixIsometry

/-! The actual terminal history span contains the flat order unit. Its
projected PSD cone is closed and positive functionals have positive history
representatives with the paper's flat-point trace/norm normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace RealInnerProductSpace Topology
namespace ScheduleLaw.History

abbrev TerminalSpace {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :=
  PrefixSpace (lastInputBurst S h)

def terminalFamilySet {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    Set (HermitianMat (TerminalSpace S h) ℂ) :=
  {M | ∃ Z : PrefixMatrices S, IsCausalPrefixFamily S Z ∧ M.mat = Z (lastInputBurst S h)}

def terminalSpan {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    Submodule ℝ (HermitianMat (TerminalSpace S h) ℂ) := Submodule.span ℝ (terminalFamilySet S h)

def terminalInputDimension {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : ℕ :=
  outputDimension S (arrived S (recordTime (lastInputBurst S h)))

theorem terminalInputDimension_pos {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    0 < terminalInputDimension S h := outputDimension_pos S _

theorem terminal_flat_mem {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    ((terminalInputDimension S h : ℝ)⁻¹ • (1 : HermitianMat (TerminalSpace S h) ℂ)) ∈
      terminalFamilySet S h := by
  refine ⟨flatPrefixFamily S,flat_prefix_causal S,?_⟩
  rw [HermitianMat.mat_smul,HermitianMat.mat_one]
  ext i j
  simp only [flatPrefixFamily,terminalInputDimension,Matrix.smul_apply,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_natCast,smul_eq_mul]

theorem terminal_identity_mem {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    (1 : HermitianMat (TerminalSpace S h) ℂ) ∈ terminalSpan S h := by
  have ht := (terminalSpan S h).smul_mem (terminalInputDimension S h : ℝ)
    (Submodule.subset_span (terminal_flat_mem S h))
  rwa [smul_smul,mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (terminalInputDimension_pos S h)),one_smul] at ht

def terminalFlatVector {I : Inventory} (S : Schedule I) (h : 0 < S.visits) : terminalSpan S h :=
  ⟨(terminalInputDimension S h : ℝ)⁻¹ • 1,Submodule.subset_span (terminal_flat_mem S h)⟩

theorem terminal_unit_flat {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    (⟨1,terminal_identity_mem S h⟩ : terminalSpan S h) =
      (terminalInputDimension S h : ℝ) • terminalFlatVector S h := by
  apply Subtype.ext
  change 1 = (terminalInputDimension S h : ℝ) • ((terminalInputDimension S h : ℝ)⁻¹ • 1)
  rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (terminalInputDimension_pos S h)),one_smul]

theorem terminal_projectedPSD_closed {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    IsClosed (projectedPositiveCone (terminalSpan S h)) :=
  isClosed_projectedPositiveCone _ (terminal_identity_mem S h)

/-- The abstract E9 representation and its port-dependent bound. This
theorem does not assume that a physical handoff/body functional factors
through the history; that separate circuit identity is still required. -/
theorem terminal_positive_representative {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (L : terminalSpan S h →ₗ[ℝ] ℝ)
    (hL : ∀ A : terminalSpan S h, 0 ≤ (A : HermitianMat (TerminalSpace S h) ℂ) → 0 ≤ L A) :
    ∃ D : HermitianMat (TerminalSpace S h) ℂ, 0 ≤ D ∧
      (∀ A : terminalSpan S h, ⟪D,(A : HermitianMat (TerminalSpace S h) ℂ)⟫_ℝ = L A) ∧
      D.trace = (terminalInputDimension S h : ℝ) * L (terminalFlatVector S h) ∧
      ‖D‖ ≤ (terminalInputDimension S h : ℝ) * L (terminalFlatVector S h) := by
  obtain ⟨D,hD,hev,ht,hn⟩ := positive_functional_representative (terminalSpan S h)
    (terminal_identity_mem S h) L hL
  have htrace : D.trace = (terminalInputDimension S h : ℝ) * L (terminalFlatVector S h) := by
    rw [ht,terminal_unit_flat,map_smul,smul_eq_mul]
  exact ⟨D,hD,hev,htrace,hn.trans_eq htrace⟩

def terminalTesterVector {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) : terminalSpan S h :=
  ⟨⟨prefixGram (lastInputBurst S h) t,(prefix_gram_positive _ t).isHermitian⟩,
    Submodule.subset_span ⟨(fun b => prefixGram b t),actual_causal_prefix_family S t,rfl⟩⟩

def terminalTesterSet {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    Set (HermitianMat (TerminalSpace S h) ℂ) :=
  {M | ∃ (r : ℕ) (t : Tester S r), M.mat = prefixGram (lastInputBurst S h) t}

theorem terminalTesterSet_eq (hcomb : CombRealization) {I : Inventory}
    (S : Schedule I) (h : 0 < S.visits) : terminalTesterSet S h = terminalFamilySet S h := by
  ext M
  constructor
  · rintro ⟨r,t,ht⟩
    exact ⟨(fun b => prefixGram b t),actual_causal_prefix_family S t,ht⟩
  · rintro ⟨Z,hZ,hM⟩
    obtain ⟨r,t,ht⟩ := realize_causal_prefix_family hcomb S Z hZ
    exact ⟨r,t,hM.trans (ht _).symm⟩

end ScheduleLaw.History
