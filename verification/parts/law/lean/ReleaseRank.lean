import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Release rank: the coding form

Formal companion to Proposition "Release rank" (b) and Appendix "Release rank" of
*The price of time order*.  For a code `C` (a subspace of `ι → K`, any field `K`) and a set `L`
of released coordinates:

* `finrank_map_restrict_add`: the code restricted to `L` has dimension
  `dim C - dim (words of C that vanish on L)`;
* `rank_submatrix_add`: for a matrix `F`, `rank F_L + dim C(R) = rank F`, where `C` is the row
  space of `F`, `F_L` keeps the columns in `L`, and `C(R)` is the subcode supported in `R = Lᶜ`;
* `helps_iff`: holding `m` coordinates lowers the cost exactly when `C` has a nonzero word of
  weight at most `m`;
* `exists_split_iff`: some set `R` of at most `m` held coordinates has `dim C(R) ≥ d` exactly
  when some subcode of dimension at least `d` has support of size at most `m`; this is the
  statement behind the generalized-Hamming-weight formula;
* `binEntropy_le_of_le`: the binary-entropy step of the classical witness.

The thermodynamic bound `Delta S_D >= rank F_L` itself is proved in the manuscript.
-/

open Module

set_option linter.unusedSectionVars false

namespace ReleaseRank

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- Restriction of a word to the coordinates in `L`. -/
abbrev restrict (L : Set ι) : (ι → K) →ₗ[K] (L → K) :=
  LinearMap.funLeft K K (Subtype.val : L → ι)

/-- The words that vanish on `L`, that is, the words supported in the complement of `L`. -/
abbrev vanishOn (L : Set ι) : Submodule K (ι → K) :=
  Submodule.pi L (fun _ => (⊥ : Submodule K K))

lemma mem_vanishOn {L : Set ι} {v : ι → K} : v ∈ vanishOn (K := K) L ↔ ∀ i ∈ L, v i = 0 := by
  simp [vanishOn, Submodule.mem_pi]

/-- Rank-nullity for the restriction of a code to the released coordinates. -/
theorem finrank_map_restrict_add (C : Submodule K (ι → K)) (L : Set ι) :
    finrank K (C.map (restrict L)) + finrank K ↥(C ⊓ vanishOn L : Submodule K (ι → K)) = finrank K C := by
  let f : C →ₗ[K] (L → K) := (restrict L).comp C.subtype
  have hrange : LinearMap.range f = C.map (restrict L) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker f = (vanishOn L).comap C.subtype := by
    ext v
    simp only [f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mem_comap,
      Submodule.coe_subtype, mem_vanishOn, restrict, LinearMap.funLeft_apply, funext_iff,
      Pi.zero_apply, Subtype.forall]
  have hkerdim : finrank K (LinearMap.ker f) = finrank K ↥(C ⊓ vanishOn L : Submodule K (ι → K)) := by
    rw [hker, ← Submodule.finrank_map_subtype_eq C, Submodule.map_comap_subtype]
  rw [← hrange, ← hkerdim]
  exact LinearMap.finrank_range_add_finrank_ker f

open Classical in
/-- For a matrix `F`, the rank of its released columns plus the dimension of the subcode
supported in the held coordinates is the rank of `F`. -/
theorem rank_submatrix_add {l : Type*} [Fintype l] (F : Matrix l ι K) (L : Set ι) :
    (F.submatrix id (Subtype.val : L → ι)).rank
      + finrank K ↥(Submodule.span K (Set.range F.row) ⊓ vanishOn L : Submodule K (ι → K)) = F.rank := by
  have hrows : Set.range (F.submatrix id (Subtype.val : L → ι)).row
      = restrict (K := K) L '' Set.range F.row := by
    ext w
    simp only [Set.mem_range, Set.mem_image, Matrix.row, Matrix.submatrix, id]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨F i, ⟨i, rfl⟩, by ext j; simp [restrict, LinearMap.funLeft_apply]⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by ext j; simp [restrict, LinearMap.funLeft_apply]⟩
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, hrows,
    Submodule.span_image]
  exact finrank_map_restrict_add _ L

open Classical in
/-- Holding at most `m` coordinates lowers the cost exactly when the code has a nonzero word of
weight at most `m`. -/
theorem helps_iff (C : Submodule K (ι → K)) (m : ℕ) :
    (∃ R : Finset ι, R.card ≤ m ∧ 0 < finrank K ↥(C ⊓ vanishOn ((R : Set ι)ᶜ) : Submodule K (ι → K))) ↔
      ∃ c ∈ C, c ≠ 0 ∧ (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ m := by
  constructor
  · rintro ⟨R, hR, hpos⟩
    have hne : C ⊓ vanishOn ((R : Set ι)ᶜ) ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hpos; exact lt_irrefl 0 hpos
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Submodule.mem_inf, mem_vanishOn] at hv
    refine ⟨v, hv.1, hv0, le_trans (Finset.card_le_card ?_) hR⟩
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hiR
    exact hi.2 (hv.2 i (by simpa using hiR))
  · rintro ⟨c, hc, hc0, hcard⟩
    refine ⟨Finset.univ.filter (fun i => c i ≠ 0), hcard, ?_⟩
    have hmem : c ∈ C ⊓ vanishOn ((↑(Finset.univ.filter (fun i => c i ≠ 0)) : Set ι)ᶜ) := by
      rw [Submodule.mem_inf, mem_vanishOn]
      refine ⟨hc, fun i hi => ?_⟩
      simpa using hi
    have hne : C ⊓ vanishOn ((↑(Finset.univ.filter (fun i => c i ≠ 0)) : Set ι)ᶜ) ≠ ⊥ := by
      intro h; rw [h, Submodule.mem_bot] at hmem; exact hc0 hmem
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.mpr hne)

open Classical in
/-- The support of a subcode: the coordinates on which some of its words is nonzero. -/
noncomputable def supp (D : Submodule K (ι → K)) : Finset ι :=
  Finset.univ.filter (fun i => ∃ v ∈ D, v i ≠ 0)

/-- Some set of at most `m` held coordinates carries a subcode of dimension at least `d` exactly
when some subcode of dimension at least `d` has support of size at most `m`. -/
theorem exists_split_iff (C : Submodule K (ι → K)) (m d : ℕ) :
    (∃ R : Finset ι, R.card ≤ m ∧ d ≤ finrank K ↥(C ⊓ vanishOn ((R : Set ι)ᶜ) : Submodule K (ι → K))) ↔
      ∃ D : Submodule K (ι → K), D ≤ C ∧ d ≤ finrank K D ∧ (supp D).card ≤ m := by
  constructor
  · rintro ⟨R, hR, hd⟩
    refine ⟨C ⊓ vanishOn ((R : Set ι)ᶜ), inf_le_left, hd, le_trans (Finset.card_le_card ?_) hR⟩
    intro i hi
    classical
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨v, hv, hvi⟩ := hi
    rw [Submodule.mem_inf, mem_vanishOn] at hv
    by_contra hiR
    exact hvi (hv.2 i (by simpa using hiR))
  · rintro ⟨D, hDC, hd, hcard⟩
    refine ⟨supp D, hcard, le_trans hd (Submodule.finrank_mono ?_)⟩
    intro v hv
    rw [Submodule.mem_inf, mem_vanishOn]
    refine ⟨hDC hv, fun i hi => ?_⟩
    by_contra hvi
    apply hi
    classical
    simp only [supp, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨v, hv, hvi⟩

/-- The binary-entropy step of the classical witness: a smaller disagreement probability, both at
most one half, gives a smaller binary entropy, so `1 - h(delta) >= 1 - h(e1 + e2)`. -/
theorem binEntropy_le_of_le {δ x : ℝ} (h0 : 0 ≤ δ) (hδx : δ ≤ x) (hx : x ≤ 2⁻¹) :
    Real.binEntropy δ ≤ Real.binEntropy x :=
  Real.binEntropy_strictMonoOn.monotoneOn ⟨h0, hδx.trans hx⟩ ⟨h0.trans hδx, hx⟩ hδx

end ReleaseRank

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms ReleaseRank.finrank_map_restrict_add
#print axioms ReleaseRank.rank_submatrix_add
#print axioms ReleaseRank.helps_iff
#print axioms ReleaseRank.exists_split_iff
#print axioms ReleaseRank.binEntropy_le_of_le
