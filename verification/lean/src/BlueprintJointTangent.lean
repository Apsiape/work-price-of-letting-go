import BlueprintWire
import BlueprintEntropyMix

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Continuity is asserted only on positive trace-one matrices. -/
theorem density_entropy_continuous (d : ℕ) :
    ContinuousOn (entropy : Mat (Fin d) → ℝ) {A | A.PosSemidef ∧ A.trace = 1} := by
  let D := {A : Mat (Fin d) // A.PosSemidef ∧ A.trace=1}
  let f : D → HermitianMat (Fin d) ℂ := fun A => ⟨A.val,A.property.1.isHermitian⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have ht : Continuous (fun A : HermitianMat (Fin d) ℂ => (A.cfc Real.negMulLog).trace) := by
    have hc : Continuous (fun A : HermitianMat (Fin d) ℂ => (A.cfc Real.negMulLog).mat) :=
      HermitianMat.continuous_mat.comp (HermitianMat.cfc_continuous Real.continuous_negMulLog)
    simpa only [HermitianMat.trace] using Complex.continuous_re.comp (Continuous.matrix_trace hc)
  rw [continuousOn_iff_continuous_restrict]
  exact (ht.comp hf).congr (fun A => by
    change ((f A).cfc Real.negMulLog).trace = entropy A.val
    rw [HermitianMat.trace_cfc_eq,entropy_of_hermitian _ A.property.1.isHermitian]
    rfl)

theorem section_entropy_maximum {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (K : Set (Mat (Fin d) × ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (hρ : SectionDensities d K) :
    ∃ z ∈ K, ∀ x ∈ K, entropy x.1/β+x.2 ≤ entropy z.1/β+z.2 := by
  have hc : ContinuousOn (fun x : Mat (Fin d) × ℝ => entropy x.1/β+x.2) K := by
    exact (((density_entropy_continuous d).comp continuous_fst.continuousOn hρ).div_const β).add
      continuous_snd.continuousOn
  exact hK.exists_isMaxOn hne hc

/-- The scalar divergent boundary slope responsible for support inclusion. -/
theorem scalar_entropy_boundary_slope :
    Tendsto (fun t : ℝ => Real.negMulLog t/t) (𝓝[>] 0) atTop := by
  have h := Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp : 0 < t := ht
  simp only [Function.comp_apply,Real.negMulLog]
  field_simp

/-- This singular-boundary claim is a priority risk check. -/
theorem maximizer_common_support {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (K : Set (Mat (Fin d) × ℝ)) (hconv : Convex ℝ K) (hρ : SectionDensities d K)
    (z : Mat (Fin d) × ℝ) (hz : z ∈ K)
    (hmax : ∀ x ∈ K, entropy x.1/β+x.2 ≤ entropy z.1/β+z.2) :
    ∀ x ∈ K, KernelContained x.1 z.1 := by
  intro x hx
  let ρ : Density (Fin d) := ⟨x.1,(hρ x hx).1,(hρ x hx).2⟩
  let ζ : Density (Fin d) := ⟨z.1,(hρ z hz).1,(hρ z hz).2⟩
  have hm := convex_section_mix_max β K hconv ρ ζ x.2 z.2 hx hz hmax
  exact (kernelContained_library_iff ρ ζ).mpr (mix_max_kernel β hβ _ _ _ _ hm)

theorem maximizer_directional_tangent {d : ℕ} (β : ℝ) (hβ : 0 < β)
    (K : Set (Mat (Fin d) × ℝ)) (hconv : Convex ℝ K) (hρ : SectionDensities d K)
    (z : Mat (Fin d) × ℝ) (hz : z ∈ K)
    (hsupp : ∀ x ∈ K, KernelContained x.1 z.1)
    (hmax : ∀ x ∈ K, entropy x.1/β+x.2 ≤ entropy z.1/β+z.2) :
    ∀ x ∈ K, x.2-energy (matrixLog z.1) x.1/β ≤ entropy z.1/β+z.2 := by
  intro x hx
  let ρ : Density (Fin d) := ⟨x.1,(hρ x hx).1,(hρ x hx).2⟩
  let ζ : Density (Fin d) := ⟨z.1,(hρ z hz).1,(hρ z hz).2⟩
  have hm := convex_section_mix_max β K hconv ρ ζ x.2 z.2 hx hz hmax
  have hk := (kernelContained_library_iff ρ ζ).mp (hsupp x hx)
  have ht := mix_max_tangent β hβ _ _ _ _ hk hm
  rw [cross_log_energy,← density_entropy_eq_library] at ht
  exact ht

theorem white_noise_faithful {d : ℕ} (hd : 0 < d) (ζ : Density (Fin d))
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (whiteNoise ζ.matrix s).PosDef ∧ (whiteNoise ζ.matrix s).trace = 1 := by
  have ha : ((1-s) • ζ.matrix).PosSemidef := ζ.positive.smul (by linarith : 0 ≤ 1-s)
  have hb : ((s/(d : ℝ)) • (1 : Mat (Fin d))).PosDef :=
    Matrix.PosDef.one.smul (div_pos hs (by exact_mod_cast hd))
  constructor
  · simpa only [whiteNoise,Complex.real_smul] using Matrix.PosDef.posSemidef_add ha hb
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    have he : (1-s)+(s/(d : ℝ))*(d : ℝ)=1 := by field_simp [hdR]; ring
    unfold whiteNoise
    rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,ζ.normalized,Matrix.trace_one]
    simpa only [Fintype.card_fin,smul_eq_mul,mul_one,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_natCast,Complex.ofReal_one] using congrArg Complex.ofReal he

/-- Positive spectral weights for an arbitrary state, with exact zero
weight on zero eigenvectors under the common-support condition. -/
theorem supported_spectral_weights {d : ℕ} (ρ ζ : Density (Fin d))
    (hS : KernelContained ρ.matrix ζ.matrix) :
    ∃ p : Fin d → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i)=1 ∧
      (∀ i, ζ.positive.isHermitian.eigenvalues i=0 → p i=0) ∧
      ∀ f : ℝ → ℝ, energy (HermitianMat.cfc (⟨ζ.matrix,ζ.positive.isHermitian⟩ : HermitianMat (Fin d) ℂ) f).mat
        ρ.matrix = ∑ i, p i*f (ζ.positive.isHermitian.eigenvalues i) := by
  let Z : HermitianMat (Fin d) ℂ := ⟨ζ.matrix,ζ.positive.isHermitian⟩
  let U : Mat (Fin d) := Z.H.eigenvectorUnitary
  let v := fun i j => U j i
  let P := fun i => pureMatrix (v i)
  let p := fun i => energy (P i) ρ.matrix
  have hP (i : Fin d) : U*Matrix.single i i 1*Uᴴ=P i := by
    ext j k
    simp [Matrix.mul_apply,Matrix.single,P,v,pureMatrix,ite_and,ite_mul,eq_comm]
  have he (f : ℝ → ℝ) : energy (Z.cfc f).mat ρ.matrix =
      ∑ i, p i*f (Z.H.eigenvalues i) := by
    rw [Z.cfc_toMat_eq_sum_smul_proj]
    change energy (∑ i, f (Z.H.eigenvalues i) • (U*Matrix.single i i 1*Uᴴ)) ρ.matrix = _
    simp_rw [hP]
    simp only [energy,Finset.sum_mul,Matrix.trace_sum,Complex.re_sum,smul_mul_assoc,
      Matrix.trace_smul,Complex.real_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,p]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨p,?_,?_,?_,he⟩
  · intro i
    have h := HermitianMat.inner_ge_zero
      (A := (⟨P i,(pureMatrix_positive (v i)).isHermitian⟩ : HermitianMat (Fin d) ℂ))
      (B := (⟨ρ.matrix,ρ.positive.isHermitian⟩ : HermitianMat (Fin d) ℂ))
      (HermitianMat.zero_le_iff.mpr (pureMatrix_positive _)) (HermitianMat.zero_le_iff.mpr ρ.positive)
    exact h
  · have h := he (fun _ => 1)
    rw [Z.cfc_const] at h
    simpa [energy,HermitianMat.mat_smul,HermitianMat.mat_one,ρ.normalized] using h.symm
  · intro i hi
    have hz : ζ.matrix *ᵥ v i=0 := by
      change ζ.matrix *ᵥ ⇑(ζ.positive.isHermitian.eigenvectorBasis i)=0
      rw [ζ.positive.isHermitian.mulVec_eigenvectorBasis,hi,zero_smul]
    have hv := hS (v i) hz
    have ht : ((P i)*ρ.matrix).trace = ∑ j, star (v i j)*(ρ.matrix *ᵥ v i) j := by
      simp only [P,pureMatrix,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.mulVec,dotProduct,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    dsimp only [p,energy]
    rw [ht,hv]
    simp

theorem supported_log_regularization {d : ℕ} (hd : 0 < d)
    (ρ ζ : Density (Fin d)) (hS : KernelContained ρ.matrix ζ.matrix)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    -energy (matrixLog (whiteNoise ζ.matrix s)) ρ.matrix ≤
      -energy (matrixLog ζ.matrix) ρ.matrix-Real.log (1-s) := by
  let Z : HermitianMat (Fin d) ℂ := ⟨ζ.matrix,ζ.positive.isHermitian⟩
  let f : ℝ → ℝ := fun x => (1-s)*x+s/(d : ℝ)
  have hw : (Z.cfc f).mat=whiteNoise ζ.matrix s := by
    dsimp only [f]
    rw [Z.cfc_add_apply,Z.cfc_const_mul_id,Z.cfc_const]
    simp only [HermitianMat.mat_add,HermitianMat.mat_smul,HermitianMat.mat_one,Complex.real_smul]
    rfl
  have hl : matrixLog (whiteNoise ζ.matrix s)=(Z.cfc (Real.log ∘ f)).mat := by
    rw [← hw]
    unfold matrixLog
    rw [dif_pos (Z.cfc f).H,← (Z.cfc f).H.cfc_eq]
    change ((Z.cfc f).cfc Real.log).mat=(Z.cfc (Real.log ∘ f)).mat
    rw [← Z.cfc_comp]
  have hz : matrixLog ζ.matrix=(Z.cfc Real.log).mat := by
    unfold matrixLog
    rw [dif_pos ζ.positive.isHermitian,← ζ.positive.isHermitian.cfc_eq]
    rfl
  obtain ⟨p,hp,hsum,hzero,he⟩ := supported_spectral_weights ρ ζ hS
  rw [hl,hz,he,he]
  have hterm (i : Fin d) : -(p i*Real.log (f (Z.H.eigenvalues i))) ≤
      -(p i*Real.log (Z.H.eigenvalues i))-p i*Real.log (1-s) := by
    by_cases hi : Z.H.eigenvalues i=0
    · have hpi := hzero i hi
      simp [hpi]
    · have hEigPos : 0 < Z.H.eigenvalues i := lt_of_le_of_ne (ζ.positive.eigenvalues_nonneg i) (Ne.symm hi)
      have ha : 0 < 1-s := sub_pos.mpr hs1
      have hb : 0 ≤ s/(d : ℝ) := div_nonneg hs.le (by positivity)
      have hm := Real.log_le_log (mul_pos ha hEigPos) (le_add_of_nonneg_right hb)
      rw [Real.log_mul ha.ne' hEigPos.ne'] at hm
      have hi' := mul_le_mul_of_nonneg_left hm (hp i)
      dsimp only [f]
      linarith
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hterm i)
  simpa only [Finset.sum_sub_distrib,Finset.sum_neg_distrib,← Finset.sum_mul,hsum,one_mul] using h

/-- The finite-dimensional joint entropy/energy certificate; every source
and every point in the same convex operational section use the same q_s. -/
theorem section_joint_reference {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (K : Set (Mat (Fin d) × ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hρ : SectionDensities d K) (τ : Density (Fin d)) (g : ℝ)
    (hg : ∀ x ∈ K, (entropy x.1-entropy τ.matrix)/β+x.2 ≤ g)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ q : Density (Fin d), q.matrix.PosDef ∧
      ∀ x ∈ K, x.2-energy (matrixLog q.matrix) x.1/β-entropy τ.matrix/β ≤
        g-Real.log (1-s)/β := by
  obtain ⟨z,hz,hm⟩ := section_entropy_maximum β hβ K hK hne hρ
  have hsupp := maximizer_common_support β hβ K hconv hρ z hz hm
  have hdir := maximizer_directional_tangent β hβ K hconv hρ z hz hsupp hm
  let ζ : Density (Fin d) := ⟨z.1,(hρ z hz).1,(hρ z hz).2⟩
  obtain ⟨hq,htr⟩ := white_noise_faithful hd ζ s hs hs1
  let q : Density (Fin d) := ⟨whiteNoise ζ.matrix s,hq.posSemidef,htr⟩
  refine ⟨q,hq,?_⟩
  intro x hx
  let ρ : Density (Fin d) := ⟨x.1,(hρ x hx).1,(hρ x hx).2⟩
  have hr := supported_log_regularization hd ρ ζ (hsupp x hx) s hs hs1
  have hdiv := div_le_div_of_nonneg_right hr hβ.le
  have hmax := hg z hz
  have htan := hdir x hx
  dsimp only [q,ζ,ρ] at hdiv ⊢
  simp only [sub_div,neg_div] at hdiv
  rw [sub_div] at hmax
  linarith

theorem section_linear_maximum {d : ℕ} (K : Set (Mat (Fin d) × ℝ))
    (hK : IsCompact K) (hne : K.Nonempty) (β : ℝ) (q : Density (Fin d)) :
    ∃ z ∈ K, ∀ x ∈ K, x.2-energy (matrixLog q.matrix) x.1/β ≤
      z.2-energy (matrixLog q.matrix) z.1/β := by
  have he : Continuous (fun x : Mat (Fin d) × ℝ => x.2-energy (matrixLog q.matrix) x.1/β) := by
    have hL := (energyLinear (matrixLog q.matrix)).continuous_of_finiteDimensional
    exact continuous_snd.sub ((hL.comp continuous_fst).div_const β)
  exact hK.exists_isMaxOn hne he.continuousOn

theorem joint_tangent {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g : ℝ) (hg : ∀ r (t : Tester S r), score β e t ≤ g)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) : TangentConclusion β e g s := by
  obtain ⟨hK,hcv,hne,hρ⟩ := operational_image_geometry e
  have hb : ∀ x ∈ OperationalImage e,
      (entropy x.1-entropy e.source.matrix)/β+x.2 ≤ g := by
    rintro x ⟨r,t,rfl⟩; exact hg r t
  obtain ⟨q,hq,hbound⟩ := section_joint_reference e.b_pos β hβ _ hK hcv hne hρ e.source g hb s hs hs1
  obtain ⟨z,hz,hm⟩ := section_linear_maximum _ hK hne β q
  obtain ⟨r,t,ht⟩ := hz
  subst z
  refine ⟨q,hq,physicalLinearized β e q t,?_,⟨r,t,rfl⟩,?_⟩
  · intro r' t'
    have h := hm _ ⟨r',t',rfl⟩
    have hp (r : ℕ) (u : Tester S r) : physicalLinearized β e q u =
        handoff e u-energy (matrixLog q.matrix) (bodyOutput e u)/β+
          energy (matrixLog q.matrix) e.source.matrix/β := by
      unfold physicalLinearized tangentHamiltonian
      rw [energy_observable_weight]
      have he : energy (matrixLog q.matrix) (bodyOutput e u-e.source.matrix) =
          energy (matrixLog q.matrix) (bodyOutput e u)-energy (matrixLog q.matrix) e.source.matrix :=
        (energyLinear _).map_sub _ _
      rw [he]
      ring
    rw [hp,hp]; dsimp at h; linarith
  · have h := hbound _ ⟨r,t,rfl⟩
    dsimp at h
    rw [physical_score_tangent_identity]
    unfold score faithfulRelativeEntropy
    have hc : energy (matrixLog q.matrix) (bodyOutput e t) =
        (bodyOutput e t*matrixLog q.matrix).trace.re := congrArg Complex.re (trace_mul_comm _ _)
    rw [hc] at h
    convert h using 1 <;> ring

end ScheduleLaw.Blueprint
