import TerminalNormalization

/-! The existing terminal history determines every earlier causal prefix.
This is a proved linear recovery map, not a replacement wire Gram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

theorem homogeneous_neg {I : Inventory} (S : Schedule I) (a : ℝ) (Z : PrefixMatrices S)
    (hZ : HomogeneousPrefixEquations S a Z) : HomogeneousPrefixEquations S (-a) (-Z) := by
  simpa only [neg_one_mul,neg_one_smul] using homogeneous_smul S a (-1) Z hZ

theorem homogeneous_zero_terminal {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (a : ℝ) (Z : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z)
    (hz : Z (lastInputBurst S h) = 0) : Z = 0 := by
  have h0 : (Z (lastInputBurst S h)).PosSemidef := by rw [hz]; exact Matrix.PosSemidef.zero
  have hp := homogeneous_prefixes_positive S h a Z hZ h0
  have hn : ((-Z) (lastInputBurst S h)).PosSemidef := by
    change (-Z (lastInputBurst S h)).PosSemidef
    rw [hz,neg_zero]
    exact Matrix.PosSemidef.zero
  have hnp := homogeneous_prefixes_positive S h (-a) (-Z) (homogeneous_neg S a Z hZ) hn
  funext b
  let M : HermitianMat (PrefixSpace b) ℂ := ⟨Z b,(hp b).isHermitian⟩
  have hM : 0 ≤ M := HermitianMat.zero_le_iff.mpr (hp b)
  have hMn : 0 ≤ -M := HermitianMat.zero_le_iff.mpr (hnp b)
  have he : M = 0 := le_antisymm (neg_nonneg.mp hMn) hM
  exact congrArg HermitianMat.mat he

theorem homogeneous_terminal_injective {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (a b : ℝ) (Z W : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z)
    (hW : HomogeneousPrefixEquations S b W)
    (he : Z (lastInputBurst S h) = W (lastInputBurst S h)) : Z = W := by
  have hd : HomogeneousPrefixEquations S (a-b) (Z-W) := by
    simpa only [sub_eq_add_neg] using homogeneous_add S a (-b) Z (-W) hZ (homogeneous_neg S b W hW)
  have hz : (Z-W) (lastInputBurst S h) = 0 := by
    change Z (lastInputBurst S h) - W (lastInputBurst S h) = 0
    rw [he,sub_self]
  exact sub_eq_zero.mp (homogeneous_zero_terminal S h (a-b) (Z-W) hd hz)

theorem terminal_mass_lift {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) : ∃ Z : PrefixMatrices S,
      HomogeneousPrefixEquations S (terminalMass S h A) Z ∧ Z (lastInputBurst S h) = A.val.mat := by
  obtain ⟨a,Z,hZ,hAZ⟩ := terminal_homogeneous_lift S h A
  rw [terminalMass_of_lift S h A a Z hZ hAZ]
  exact ⟨Z,hZ,hAZ⟩

def terminalPrefixFamily {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) : PrefixMatrices S := Classical.choose (terminal_mass_lift S h A)

theorem terminalPrefixFamily_spec {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (A : terminalSpan S h) :
    HomogeneousPrefixEquations S (terminalMass S h A) (terminalPrefixFamily S h A) ∧
      terminalPrefixFamily S h A (lastInputBurst S h) = A.val.mat :=
  Classical.choose_spec (terminal_mass_lift S h A)

def terminalPrefixReadout {I : Inventory} (S : Schedule I) (h : 0 < S.visits) :
    terminalSpan S h →ₗ[ℝ] PrefixMatrices S where
  toFun := terminalPrefixFamily S h
  map_add' A B := by
    apply homogeneous_terminal_injective S h (terminalMass S h (A+B))
      (terminalMass S h A+terminalMass S h B) _ _ (terminalPrefixFamily_spec S h (A+B)).1
      (homogeneous_add S _ _ _ _ (terminalPrefixFamily_spec S h A).1 (terminalPrefixFamily_spec S h B).1)
    change terminalPrefixFamily S h (A+B) (lastInputBurst S h) =
      terminalPrefixFamily S h A (lastInputBurst S h) + terminalPrefixFamily S h B (lastInputBurst S h)
    rw [(terminalPrefixFamily_spec S h (A+B)).2,(terminalPrefixFamily_spec S h A).2,
      (terminalPrefixFamily_spec S h B).2]
    rfl
  map_smul' a A := by
    apply homogeneous_terminal_injective S h (terminalMass S h (a • A))
      (a * terminalMass S h A) _ _ (terminalPrefixFamily_spec S h (a • A)).1
      (homogeneous_smul S _ a _ (terminalPrefixFamily_spec S h A).1)
    change terminalPrefixFamily S h (a • A) (lastInputBurst S h) =
      a • terminalPrefixFamily S h A (lastInputBurst S h)
    rw [(terminalPrefixFamily_spec S h (a • A)).2,(terminalPrefixFamily_spec S h A).2]
    rfl

theorem terminalPrefixReadout_actual {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r : ℕ} (t : Tester S r) :
    terminalPrefixReadout S h (terminalTesterVector S h t) = (fun b => prefixGram b t) := by
  exact homogeneous_terminal_injective S h _ 1 _ _
    (terminalPrefixFamily_spec S h (terminalTesterVector S h t)).1
    (homogeneous_of_causal S _ (actual_causal_prefix_family S t))
    (terminalPrefixFamily_spec S h (terminalTesterVector S h t)).2

theorem actual_prefixes_eq_of_terminal_eq {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    {r q : ℕ} (t : Tester S r) (u : Tester S q)
    (he : prefixGram (lastInputBurst S h) t = prefixGram (lastInputBurst S h) u) :
    (fun b => prefixGram b t) = (fun b => prefixGram b u) :=
  homogeneous_terminal_injective S h 1 1 _ _
    (homogeneous_of_causal S _ (actual_causal_prefix_family S t))
    (homogeneous_of_causal S _ (actual_causal_prefix_family S u)) he

end ScheduleLaw.History
