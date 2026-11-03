import BlueprintContracts
import ClassicalFlag
import FiniteTensorMatrix
import FiniteRoundingSelection

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FiniteResidue

/-- A physical flat projector with n(i) occupied residue labels above i. -/
def fiberProjection {a : Type} [Fintype a] [DecidableEq a]
    (n : a → ℕ) (R : ℕ) : Mat (a × Fin R) :=
  diagonal (fun x => if x.2.val < n x.1 then 1 else 0)

/-- Exact square-matrix and marginal contract; the actual residue is Fin R. -/
theorem fiber_projection_spec {a : Type} [Fintype a] [DecidableEq a]
    (n : a → ℕ) (R : ℕ) (hn : ∀ i, n i ≤ R) (K : ℕ) (hK : K = ∑ i, n i) :
    (fiberProjection n R).IsHermitian ∧
      fiberProjection n R * fiberProjection n R = fiberProjection n R ∧
      (fiberProjection n R).trace = (K : ℂ) ∧
      partialRight (((K : ℂ)⁻¹) • fiberProjection n R) =
        diagonal (fun i => ((n i : ℝ)/(K : ℝ) : ℂ)) := by
  classical
  have hcount (i : a) : (∑ j : Fin R, if j.val < n i then (1 : ℂ) else 0) = (n i : ℂ) := by
    let e : {j : Fin R // j.val < n i} ≃ Fin (n i) := {
      toFun := fun j => ⟨j.1.val,j.2⟩
      invFun := fun j => ⟨⟨j.val,lt_of_lt_of_le j.isLt (hn i)⟩,j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hc := Fintype.card_congr e
    rw [Fintype.card_subtype,Fintype.card_fin] at hc
    rw [← Finset.sum_filter]
    simp [hc]
  refine ⟨?_,?_,?_,?_⟩
  · apply Matrix.PosSemidef.isHermitian
    apply Matrix.PosSemidef.diagonal
    intro x
    by_cases hx : x.2.val < n x.1 <;> simp [hx]
  · unfold fiberProjection
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext x
    by_cases hx : x.2.val < n x.1 <;> simp [hx]
  · simp only [fiberProjection,trace_diagonal]
    rw [Fintype.sum_prod_type]
    simp_rw [hcount]
    rw [← Nat.cast_sum,← hK]
  · ext i j
    by_cases hij : i=j
    · subst j
      simp only [partialRight,fiberProjection,Matrix.smul_apply,smul_eq_mul,diagonal_apply_eq]
      rw [← Finset.mul_sum,hcount]
      simp only [Complex.ofReal_natCast,div_eq_mul_inv]
      ring
    · simp [partialRight,fiberProjection,Matrix.diagonal,hij]

/-- Subnormalized integer counts below p give a normalized code whose
trace-distance loss is at most its omitted mass. No residue is traced
out before the physical projector is constructed. -/
theorem dominated_normalization_error {a : Type} [Fintype a] [DecidableEq a]
    (p : a → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n : a → ℕ) (K : ℕ) (hK : K = ∑ i, n i) (hKpos : 0 < K)
    (M : ℝ) (hM : 0 < M) (hdom : ∀ i, (n i : ℝ)/M ≤ p i) :
    traceDistance (diagonal (fun i => ((n i : ℝ)/(K : ℝ) : ℂ)))
      (diagonal (fun i => (p i : ℂ))) ≤ 1-(K : ℝ)/M := by
  classical
  simp only [← Complex.ofReal_div]
  have hk : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hsum : (∑ i, (n i : ℝ)) = (K : ℝ) := by exact_mod_cast hK.symm
  have hKM : (K : ℝ)/M ≤ 1 := by
    calc (K : ℝ)/M = ∑ i, (n i : ℝ)/M := by rw [← Finset.sum_div,hsum]
         _ ≤ ∑ i, p i := Finset.sum_le_sum (fun i _ => hdom i)
         _ = 1 := hs
  have hkM : (K : ℝ) ≤ M := (div_le_one hM).mp hKM
  let A : Mat a := diagonal (fun i => (((n i : ℝ)/(K : ℝ) : ℝ) : ℂ))
  let B : Mat a := diagonal (fun i => (p i : ℂ))
  let C : Mat a := diagonal (fun i => (((n i : ℝ)/M : ℝ) : ℂ))
  have hnorm (D : Mat a) (hD : D.PosSemidef) : Matrix.traceNorm D = D.trace.re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hD.traceNorm_eq_trace
  have hA : (A-C).PosSemidef := by
    dsimp only [A,C]
    rw [diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ _ - _
    rw [← Complex.ofReal_sub]
    exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr
      (div_le_div_of_nonneg_left (by positivity) hk hkM),rfl⟩
  have hB : (B-C).PosSemidef := by
    dsimp only [B,C]
    rw [diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ _ - _
    rw [← Complex.ofReal_sub]
    exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hdom i),rfl⟩
  have htrA : A.trace.re = 1 := by
    simp only [A,trace_diagonal,Complex.re_sum,Complex.ofReal_re,← Finset.sum_div,hsum]
    exact div_self hk.ne'
  have htrB : B.trace.re = 1 := by
    have hpp (i : a) : 0 ≤ (p i : ℂ) := Complex.nonneg_iff.mpr ⟨hp i,rfl⟩
    have hbpos : B.PosSemidef := Matrix.PosSemidef.diagonal hpp
    let target : Density a := ⟨B,hbpos,by simp [B,trace_diagonal,← Complex.ofReal_sum,hs]⟩
    simpa only [Complex.one_re] using congrArg Complex.re target.normalized
  have htrC : C.trace.re = (K : ℝ)/M := by
    simp only [C,trace_diagonal,Complex.re_sum,Complex.ofReal_re,← Finset.sum_div,hsum]
  have he : A-B=(A-C)+-(B-C) := by abel
  have ht := Matrix.traceNorm_add_le (A-C) (-(B-C))
  rw [← he,Matrix.traceNorm_neg,hnorm _ hA,hnorm _ hB] at ht
  simp only [trace_sub,Complex.sub_re,htrA,htrB,htrC] at ht
  change traceNorm (A-B)/2 ≤ _
  rw [ClassicalFlag.traceNorm_eq_library]
  linarith

/-- The finite loss estimate that combines atypical mass and integer rounding. -/
theorem rounded_counts_loss {a : Type} [Fintype a] [DecidableEq a]
    (p : a → ℝ) (hp : ∀ i, 0 ≤ p i) (T : Finset a)
    (M : ℝ) (hM : 0 < M) :
    let n : a → ℕ := fun i => if i ∈ T then ⌊M*p i⌋₊ else 0
    (∀ i, (n i : ℝ)/M ≤ p i) ∧
      1-((∑ i, n i : ℕ) : ℝ)/M ≤
        (1-∑ i ∈ T, p i)+(T.card : ℝ)/M := by
  classical
  dsimp only
  constructor
  · intro i
    by_cases hi : i ∈ T
    · simp only [if_pos hi]
      exact (div_le_iff₀ hM).mpr (by
        simpa only [mul_comm] using Nat.floor_le (mul_nonneg hM.le (hp i)))
    · simp only [if_neg hi,Nat.cast_zero,zero_div]
      exact hp i
  · have hsum : ((∑ i : a, if i ∈ T then ⌊M*p i⌋₊ else 0 : ℕ) : ℝ) =
        ∑ i ∈ T, (⌊M*p i⌋₊ : ℝ) := by
      simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
      rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
    have hlo : M*(∑ i ∈ T, p i)-(T.card : ℝ) ≤ ∑ i ∈ T, (⌊M*p i⌋₊ : ℝ) := by
      calc M*(∑ i ∈ T, p i)-(T.card : ℝ) = ∑ i ∈ T, (M*p i-1) := by
             rw [Finset.sum_sub_distrib,← Finset.mul_sum]
             simp
           _ ≤ _ := Finset.sum_le_sum (fun i _ => by linarith [Nat.lt_floor_add_one (M*p i)])
    rw [hsum]
    have hdiv := div_le_div_of_nonneg_right hlo hM.le
    have he : (M*(∑ i ∈ T, p i)-(T.card : ℝ))/M =
        (∑ i ∈ T, p i)-(T.card : ℝ)/M := by
      field_simp
    rw [he] at hdiv
    linarith

/-- Finite bounded-residue assembly. Its hypotheses are numeric probability
and capacity conditions, not any author conversion or coding theorem. -/
theorem finite_rounded_code {a : Type} [Fintype a] [DecidableEq a]
    (p : a → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (T : Finset a) (M : ℝ) (hM : 0 < M) (R : ℕ)
    (hcap : ∀ i ∈ T, ⌊M*p i⌋₊ ≤ R)
    (hpos : 0 < ∑ i, (if i ∈ T then ⌊M*p i⌋₊ else 0)) :
    ∃ (K : ℕ) (P : Mat (a × Fin R)), 0 < K ∧
      K = ∑ i, (if i ∈ T then ⌊M*p i⌋₊ else 0) ∧
      P.IsHermitian ∧ P*P=P ∧ P.trace=(K : ℂ) ∧
      traceDistance (partialRight (((K : ℂ)⁻¹) • P))
        (diagonal (fun i => (p i : ℂ))) ≤
          (1-∑ i ∈ T, p i)+(T.card : ℝ)/M := by
  classical
  let n : a → ℕ := fun i => if i ∈ T then ⌊M*p i⌋₊ else 0
  let K := ∑ i, n i
  have hcap' (i : a) : n i ≤ R := by
    by_cases hi : i ∈ T
    · simpa [n,hi] using hcap i hi
    · simp [n,hi]
  obtain ⟨hH,hId,hTr,hMarg⟩ := fiber_projection_spec n R hcap' K rfl
  obtain ⟨hdom,hloss⟩ := rounded_counts_loss p hp T M hM
  refine ⟨K,fiberProjection n R,hpos,rfl,hH,hId,hTr,?_⟩
  rw [hMarg]
  exact (dominated_normalization_error p hp hs n K rfl hpos M hM hdom).trans hloss

/-- Actual product-spectrum probability in the single-copy eigenbasis. -/
def spectralWord {d : ℕ} (τ : Density (Fin d)) (m : ℕ)
    (x : Fin (m+1) → Fin d) : ℝ :=
  ∏ j, τ.positive.isHermitian.eigenvalues (x j)

theorem tensor_spectral_basis {d : ℕ} (τ : Density (Fin d)) (m : ℕ) :
    ∃ U : Mat (Fin (m+1) → Fin d), IsUnitary U ∧
      tensorPower τ.matrix (m+1) =
        evolve U (diagonal (fun x => (spectralWord τ m x : ℂ))) := by
  classical
  let U₀ : Mat (Fin d) := τ.positive.isHermitian.eigenvectorUnitary
  have hU₀ : IsUnitary U₀ :=
    ⟨τ.positive.isHermitian.eigenvectorUnitary.2.1,
      τ.positive.isHermitian.eigenvectorUnitary.2.2⟩
  have hspec : τ.matrix = evolve U₀
      (diagonal (fun i => (τ.positive.isHermitian.eigenvalues i : ℂ))) := by
    simpa only [evolve,U₀,Unitary.conjStarAlgAut_apply,star_eq_conjTranspose]
      using τ.positive.isHermitian.spectral_theorem
  refine ⟨tensorMatrix U₀ (m+1),tensorMatrix_unitary U₀ hU₀ (m+1),?_⟩
  have hm := congrArg (fun A => tensorMatrix A (m+1)) hspec
  dsimp only at hm
  rw [tensorMatrix_evolve,tensorMatrix_diagonal] at hm
  simpa only [tensorPower,tensorMatrix,spectralWord,Complex.ofReal_prod] using hm

/-- Exact finite matrix transport, including the full residue register. -/
theorem spectral_rounded_code {d : ℕ} (τ : Density (Fin d)) (m : ℕ)
    (T : Finset (Fin (m+1) → Fin d)) (M : ℝ) (hM : 0 < M) (R : ℕ)
    (hcap : ∀ x ∈ T, ⌊M*spectralWord τ m x⌋₊ ≤ R)
    (hpos : 0 < ∑ x, (if x ∈ T then ⌊M*spectralWord τ m x⌋₊ else 0)) :
    ∃ (K : ℕ) (V P : Mat ((Fin (m+1) → Fin d) × Fin R)),
      0 < K ∧ K = ∑ x, (if x ∈ T then ⌊M*spectralWord τ m x⌋₊ else 0) ∧
      IsUnitary V ∧ P.IsHermitian ∧ P*P=P ∧ P.trace=(K : ℂ) ∧
      traceDistance (partialRight (evolve V (((K : ℂ)⁻¹) • P)))
        (tensorPower τ.matrix (m+1)) ≤
          (1-∑ x ∈ T, spectralWord τ m x)+(T.card : ℝ)/M := by
  classical
  have hp (x : Fin (m+1) → Fin d) : 0 ≤ spectralWord τ m x :=
    Finset.prod_nonneg (fun i _ => τ.positive.eigenvalues_nonneg (x i))
  have hs : ∑ x, spectralWord τ m x = 1 := by
    unfold spectralWord
    rw [← Fintype.prod_sum]
    simp only [density_eigenvalues_sum,Finset.prod_const_one]
  obtain ⟨K,P,hK,hKeq,hP,hPi,hTr,hErr⟩ :=
    finite_rounded_code (spectralWord τ m) hp hs T M hM R hcap hpos
  obtain ⟨U,hU,hSpec⟩ := tensor_spectral_basis τ m
  have hOne : IsUnitary (1 : Mat (Fin R)) := by constructor <;> simp
  refine ⟨K,U ⊗ₖ (1 : Mat (Fin R)),P,hK,hKeq,
    unitary_kron hU hOne,hP,hPi,hTr,?_⟩
  rw [partialRight_evolve_kron_one,hSpec,traceDistance_unitary _ _ _ hU]
  exact hErr

/-- All iid data and rates needed by the small-residue assembly. Its
existence is a visible proof obligation, not a premise of the work law. -/
structure TypicalRoundingData {d : ℕ} (τ : Density (Fin d)) where
  typical : (m : ℕ) → Finset (Fin (m+1) → Fin d)
  scale : ℕ → ℝ
  scale_pos : ∀ m, 0 < scale m
  residue : ℕ → ℕ
  residue_pos : ∀ m, 0 < residue m
  capacity : ∀ m x, x ∈ typical m →
    ⌊scale m * spectralWord τ m x⌋₊ ≤ residue m
  rank_pos : ∀ m, 0 < ∑ x,
    (if x ∈ typical m then ⌊scale m * spectralWord τ m x⌋₊ else 0)
  rank_rate : Tendsto (fun m => Real.log ((∑ x,
    (if x ∈ typical m then ⌊scale m * spectralWord τ m x⌋₊ else 0) : ℕ) : ℝ)
      / (m+1 : ℝ)) atTop (𝓝 (entropy τ.matrix))
  residue_rate : Tendsto (fun m => Real.log (residue m : ℝ)/(m+1 : ℝ)) atTop (𝓝 0)
  loss_nonneg : ∀ m, 0 ≤ (1-∑ x ∈ typical m, spectralWord τ m x)
    +((typical m).card : ℝ)/scale m
  loss_vanishes : Vanishes (fun m => (1-∑ x ∈ typical m, spectralWord τ m x)
    +((typical m).card : ℝ)/scale m)

/-- Finite iid spectral concentration and simultaneous rate selection. -/
theorem typical_rounding_data {d : ℕ} (τ : Density (Fin d)) :
    Nonempty (TypicalRoundingData τ) := by
  classical
  let p : Fin d → ℝ := τ.positive.isHermitian.eigenvalues
  let S := entropy τ.matrix
  have hp0 : ∀ i, 0 ≤ p i := τ.positive.eigenvalues_nonneg
  have hp : ∑ i, p i = 1 := density_eigenvalues_sum τ
  have hS : S = ∑ i, p i * (-Real.log (p i)) := by
    dsimp only [S,p]
    rw [entropy_of_hermitian _ τ.positive.isHermitian]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Real.negMulLog]
    ring
  have hstage (j : ℕ) : ∃ N : ℕ, ∀ m, N ≤ m →
      ∃ D : FiniteIID.PointRounding p (m+1),
        |Real.log (D.count : ℝ)/(m+1 : ℝ)-S| ≤ 1/(j+1 : ℝ) ∧
        Real.log (D.R : ℝ)/(m+1 : ℝ) ≤ 1/(j+1 : ℝ) ∧ D.error ≤ 1/(j+1 : ℝ) := by
    exact eventually_atTop.mp (FiniteIID.eventually_point p hp0 hp S hS
      (1/(j+1 : ℝ)) (by positivity))
  choose N hN using hstage
  let index := diagonalIndex N
  have hi : Tendsto index atTop atTop := diagonalIndex_tendsto N
  have hne : ∀ᶠ m : ℕ in atTop, index m ≠ 0 := by
    filter_upwards [hi.eventually (eventually_gt_atTop 0)] with m hm
    omega
  have hselect (m : ℕ) : ∃ D : FiniteIID.PointRounding p (m+1), index m ≠ 0 →
      |Real.log (D.count : ℝ)/(m+1 : ℝ)-S| ≤ 1/(index m+1 : ℝ) ∧
      Real.log (D.R : ℝ)/(m+1 : ℝ) ≤ 1/(index m+1 : ℝ) ∧
      D.error ≤ 1/(index m+1 : ℝ) := by
    by_cases hz : index m = 0
    · obtain ⟨D⟩ := FiniteIID.point_exists p hp (m+1)
      exact ⟨D,fun h => (h hz).elim⟩
    · have hNm : N (index m) ≤ m := (diagonalIndex_spec N m).resolve_left hz
      obtain ⟨D,hD⟩ := hN (index m) m hNm
      exact ⟨D,fun _ => hD⟩
  choose D hD using hselect
  have heps : Tendsto (fun m => 1/(index m+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hi
  refine ⟨{
    typical := fun m => (D m).event
    scale := fun m => (D m).M
    scale_pos := fun m => (D m).M_pos
    residue := fun m => (D m).R
    residue_pos := fun m => (D m).R_pos
    capacity := fun m => (D m).capacity
    rank_pos := fun m => (D m).rank_pos
    rank_rate := ?_
    residue_rate := ?_
    loss_nonneg := fun m => (D m).error_nonneg hp0 hp
    loss_vanishes := ?_ }⟩
  · change Tendsto (fun m => Real.log ((D m).count : ℝ)/(m+1 : ℝ)) atTop (𝓝 S)
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero' (Eventually.of_forall (fun m => abs_nonneg _)) _ heps
    filter_upwards [hne] with m hm
    exact (hD m hm).1
  · have hnon (m : ℕ) : 0 ≤ Real.log ((D m).R : ℝ)/(m+1 : ℝ) := by
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (D m).R_pos))
        (by positivity)
    apply squeeze_zero' (Eventually.of_forall hnon) _ heps
    filter_upwards [hne] with m hm
    exact (hD m hm).2.1
  · change Tendsto (fun m => (D m).error) atTop (𝓝 0)
    apply squeeze_zero' (Eventually.of_forall (fun m => (D m).error_nonneg hp0 hp)) _ heps
    filter_upwards [hne] with m hm
    exact (hD m hm).2.2

end ScheduleLaw.Blueprint.FiniteResidue
