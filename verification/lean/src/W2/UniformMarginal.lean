import W2.TensorFamily
import PrefixPurification

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw.Blueprint.W2

theorem pureMatrix_idempotent {a : Type} [Fintype a] (ψ : a → ℂ)
    (hψ : (pureMatrix ψ).trace=1) : pureMatrix ψ*pureMatrix ψ=pureMatrix ψ := by
  ext i j
  change (∑ l, (ψ i*star (ψ l))*(ψ l*star (ψ j)))=ψ i*star (ψ j)
  calc (∑ l, (ψ i*star (ψ l))*(ψ l*star (ψ j)))
      = ψ i*(∑ l,ψ l*star (ψ l))*star (ψ j) := by
        simp only [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l hl
        ring
    _ = ψ i*star (ψ j) := by
      change ψ i*(pureMatrix ψ).trace*star (ψ j)=_
      rw [hψ,mul_one]

theorem uniform_projector_marginal {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Density a) (k : ℕ) (hk : 0 < k) :
    ∃ r : ℕ, 0 < r ∧ ∃ P : Mat (a × Fin r),
      P.IsHermitian ∧ P*P=P ∧ P.trace=(k : ℂ) ∧
      partialRight (((k : ℂ)⁻¹) • P)=ρ.matrix := by
  classical
  haveI : Nonempty a := by
    by_contra h
    haveI : IsEmpty a := not_nonempty_iff.mp h
    have ht := ρ.normalized
    simp at ht
  haveI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let r := Fintype.card (a × Fin k)
  let er : Fin r ≃ a × Fin k := (Fintype.equivFin (a × Fin k)).symm
  let e : (a × Fin r) ≃ ((a × a) × Fin k) :=
    (Equiv.prodCongr (Equiv.refl a) er).trans (Equiv.prodAssoc a a (Fin k)).symm
  let ψ := ρ.toMState.purify
  let M := pureMatrix ψ.vec
  let P := (M ⊗ₖ (1 : Mat (Fin k))).submatrix e e
  have hMt : M.trace=1 := by
    change (pureMatrix ψ.vec).trace=1
    rw [pureMatrix_trace]
    have hn : ∑ i,Complex.normSq (ψ.vec i)=1 := by
      simpa only [Complex.normSq_eq_norm_sq,Ket.coe_fun_eq] using ψ.normalized
    rw [hn,Complex.ofReal_one]
  have hMi : M*M=M := pureMatrix_idempotent ψ.vec hMt
  have hMarg : partialRight M=ρ.matrix := History.density_purification_matrix ρ.toMState
  have hPt : P.trace=(k : ℂ) := by
    change (∑ x : a × Fin r,(M ⊗ₖ (1 : Mat (Fin k))) (e x) (e x))=(k : ℂ)
    rw [Equiv.sum_comp e (fun y => (M ⊗ₖ (1 : Mat (Fin k))) y y)]
    change (M ⊗ₖ (1 : Mat (Fin k))).trace=(k : ℂ)
    rw [trace_kronecker,hMt,one_mul,trace_one,Fintype.card_fin]
  have hPr : partialRight P=(k : ℂ) • ρ.matrix := by
    ext i j
    change (∑ l : Fin r,P (i,l) (j,l))=(k : ℂ)*ρ.matrix i j
    simp only [P,Matrix.submatrix_apply,e,Equiv.trans_apply,Equiv.prodCongr_apply,
      Equiv.refl_apply,Equiv.prodAssoc_symm_apply,Prod.map,Matrix.kroneckerMap_apply,
      Matrix.one_apply_eq,mul_one]
    rw [Equiv.sum_comp er (fun y : a × Fin k => M (i,y.1) (j,y.1))]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.mul_sum]
    change (k : ℂ)*(partialRight M) i j=(k : ℂ)*ρ.matrix i j
    rw [hMarg]
  refine ⟨r,Fintype.card_pos,P,?_,?_,hPt,?_⟩
  · exact ((pureMatrix_positive ψ.vec).kronecker Matrix.PosSemidef.one).isHermitian.submatrix e
  · change ((M ⊗ₖ (1 : Mat (Fin k))).submatrix e e)*
        ((M ⊗ₖ (1 : Mat (Fin k))).submatrix e e)=_
    rw [submatrix_mul_equiv,← mul_kronecker_mul,hMi,mul_one]
  · rw [ClassicalFlag.partialRight_weight,hPr,smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hk.ne'),one_smul]

theorem entropy_rank_sequence (s : ℝ) (hs : 0 ≤ s) :
    ∃ k : ℕ → ℕ, (∀ m,0 < k m) ∧
      Tendsto (fun m => Real.log (k m : ℝ)/(m+1 : ℝ)) atTop (𝓝 s) := by
  let k : ℕ → ℕ := fun m => ⌈Real.exp (((m : ℝ)+1)*s)⌉₊
  have hkp (m : ℕ) : 0 < k m := Nat.ceil_pos.mpr (Real.exp_pos _)
  refine ⟨k,hkp,?_⟩
  have hbounds (m : ℕ) :
      s ≤ Real.log (k m : ℝ)/(m+1 : ℝ) ∧
      Real.log (k m : ℝ)/(m+1 : ℝ) ≤ s+Real.log 2/(m+1 : ℝ) := by
    let t := ((m : ℝ)+1)*s
    have ht : 0 ≤ t := mul_nonneg (by positivity) hs
    have hkle : (k m : ℝ) ≤ 2*Real.exp t := by
      have ha := Nat.ceil_lt_add_one (Real.exp_pos t).le
      have hb : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
      dsimp [k,t] at *
      linarith
    have hlow := Real.log_le_log (Real.exp_pos t) (Nat.le_ceil (Real.exp t))
    have hupp := Real.log_le_log (by exact_mod_cast hkp m : (0 : ℝ) < k m) hkle
    rw [Real.log_exp] at hlow
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero t),Real.log_exp] at hupp
    constructor
    · apply (le_div_iff₀ (by positivity : (0 : ℝ) < m+1)).mpr
      dsimp [t] at hlow
      nlinarith [hlow]
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < m+1)).mpr
      dsimp [t] at hupp
      have hne : (m+1 : ℝ) ≠ 0 := by positivity
      rw [add_mul,div_mul_cancel₀ _ hne]
      nlinarith [hupp]
  have he : Tendsto (fun m : ℕ => Real.log 2/(m+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 2)
  have hu : Tendsto (fun m : ℕ => s+Real.log 2/(m+1 : ℝ)) atTop (𝓝 s) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun m => (hbounds m).1) (fun m => (hbounds m).2)

theorem traceDistance_self {a : Type} [Fintype a] [DecidableEq a] (ρ : Mat a) :
    traceDistance ρ ρ=0 := by
  have hz : (posSemidef_conjTranspose_mul_self (0 : Mat a)).isHermitian.eigenvalues=0 :=
    Matrix.IsHermitian.eigenvalues_eq_zero_iff _ |>.mpr (by simp)
  unfold traceDistance
  rw [sub_self]
  unfold traceNorm
  rw [hz]
  simp

end ScheduleLaw.Blueprint.W2
