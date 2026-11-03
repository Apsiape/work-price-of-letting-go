import BlueprintJointTangent
import FinalSlackEffect
import ThermalContactEnergy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
open scoped MatrixOrder
namespace ScheduleLaw.Blueprint
open History

@[reducible]
def matrixCStarAlgebra (d : ℕ) : CStarAlgebra (Mat (Fin d)) := {}
attribute [local instance] matrixCStarAlgebra
def matrixSqrt {d : ℕ} (A : Mat (Fin d)) : Mat (Fin d) :=
  if h : A.IsHermitian then h.cfc Real.sqrt else 0

theorem matrixSqrt_eq_cfc {d : ℕ} (A : Mat (Fin d)) (hA : A.IsHermitian) :
    matrixSqrt A = cfc Real.sqrt A := by
  rw [matrixSqrt, dif_pos hA, hA.cfc_eq]

theorem matrixSqrt_hermitian {d : ℕ} (A : Mat (Fin d)) (hA : A.IsHermitian) :
    (matrixSqrt A).IsHermitian := by
  rw [matrixSqrt_eq_cfc A hA]
  exact cfc_predicate Real.sqrt A

theorem matrixSqrt_mul_self {d : ℕ} (A : Mat (Fin d)) (hA : A.PosSemidef) :
    matrixSqrt A * matrixSqrt A = A := by
  rw [matrixSqrt_eq_cfc A hA.isHermitian, ← cfc_mul Real.sqrt Real.sqrt A]
  calc cfc (fun x : ℝ => Real.sqrt x * Real.sqrt x) A = cfc (id : ℝ → ℝ) A := by
         apply cfc_congr
         intro x hx
         exact Real.mul_self_sqrt
           ((StarOrderedRing.nonneg_iff_spectrum_nonneg A hA.isHermitian).mp hA.nonneg x hx)
       _ = A := cfc_id ℝ A hA.isHermitian

theorem matrixSqrt_commute {d : ℕ} (A B : Mat (Fin d))
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    Commute (matrixSqrt A) (matrixSqrt B) := by
  rw [matrixSqrt_eq_cfc A hA, matrixSqrt_eq_cfc B hB]
  exact ((hAB.cfc_real Real.sqrt).symm.cfc_real Real.sqrt).symm

theorem matrixSqrt_norm_le_one {d : ℕ} (A : Mat (Fin d)) (hA : A.IsHermitian)
    (hn : ‖A‖ ≤ 1) : ‖matrixSqrt A‖ ≤ 1 := by
  rw [matrixSqrt_eq_cfc A hA]
  apply norm_cfc_le zero_le_one
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
  exact Real.sqrt_le_one.mpr ((Real.le_norm_self x).trans ((IsometricContinuousFunctionalCalculus.norm_spectrum_le A hx hA).trans hn))

/-- The square-root channel has a linear, rather than square-root, remainder
when the other branch is the complementary effect. -/
theorem matrixSqrt_sub_one_norm {d : ℕ} (A : Mat (Fin d))
    (hA : A.PosSemidef) (hn : ‖A‖ ≤ 1) : ‖matrixSqrt A - 1‖ ≤ ‖A - 1‖ := by
  have hc : cfc (fun x : ℝ => Real.sqrt x - 1) A = matrixSqrt A - 1 := by
    rw [cfc_sub, ← matrixSqrt_eq_cfc A hA.isHermitian,
      cfc_const_one ℝ A (show IsSelfAdjoint A from hA.isHermitian)]
  rw [← hc]
  apply norm_cfc_le (norm_nonneg _)
  intro x hx
  have hx0 := (StarOrderedRing.nonneg_iff_spectrum_nonneg A hA.isHermitian).mp hA.nonneg x hx
  have hx1 : x ≤ 1 := (Real.le_norm_self x).trans ((IsometricContinuousFunctionalCalculus.norm_spectrum_le A hx hA.isHermitian).trans hn)
  have hs1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1
  have hxs : x ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
  have hl : cfc (fun y : ℝ => y - 1) A = A - 1 := by
    rw [cfc_sub]
    change cfc (id : ℝ → ℝ) A - cfc (fun _ : ℝ => 1) A = A - 1
    rw [cfc_id ℝ A (show IsSelfAdjoint A from hA.isHermitian),
      cfc_const_one ℝ A (show IsSelfAdjoint A from hA.isHermitian)]
  calc ‖Real.sqrt x - 1‖ ≤ ‖x - 1‖ := by
         rw [Real.norm_eq_abs, Real.norm_eq_abs,
           abs_of_nonpos (sub_nonpos.mpr hs1), abs_of_nonpos (sub_nonpos.mpr hx1)]
         linarith
       _ ≤ ‖A - 1‖ := by
         simpa only [hl] using norm_apply_le_norm_cfc (fun y : ℝ => y - 1) A hx (by fun_prop)
           (show IsSelfAdjoint A from hA.isHermitian)

theorem hot_effect_properties {d : ℕ} (D : Mat (Fin d)) (hD : D.PosSemidef)
    (M : ℝ) (hM : 0 < M) (hbig : 2*‖D‖ ≤ M) :
    let A := ((M⁻¹ : ℝ) : ℂ) • D
    A.PosSemidef ∧ (1-A).PosSemidef ∧ ‖A‖ = ‖D‖/M ∧ ‖A‖ ≤ 1 ∧ ‖1-A‖ ≤ 1 := by
  dsimp only
  let A := ((M⁻¹ : ℝ) : ℂ) • D
  have ha : A.PosSemidef := by
    simpa only [A, Matrix.smul_apply, Complex.real_smul] using hD.smul (inv_nonneg.mpr hM.le)
  have he : ‖A‖ = ‖D‖/M := by
    simp only [A, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM), div_eq_mul_inv, mul_comm]
  have hn : ‖A‖ ≤ 1 := by
    rw [he, div_le_one hM]
    linarith [norm_nonneg D]
  have ha1 : A ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A ha.nonneg).mp hn
  have hb : (1-A).PosSemidef := ha1
  have hb1 : 1-A ≤ 1 := sub_le_self 1 ha.nonneg
  exact ⟨ha, hb, he, hn, (CStarAlgebra.norm_le_one_iff_of_nonneg (1-A) hb.nonneg).mpr hb1⟩

def hotProbability (β M : ℝ) : ℝ := (1+Real.exp (β*M))⁻¹

theorem hotProbability_tendsto_zero (β : ℝ) (hβ : 0 < β) :
    Tendsto (hotProbability β) atTop (𝓝 0) := by
  have he : Tendsto (fun M : ℝ => Real.exp (β*M)+1) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβ)).atTop_add tendsto_const_nhds
  simpa only [hotProbability, Function.comp_def, add_comm] using tendsto_inv_atTop_zero.comp he

theorem hot_remainder_tendsto_zero (β h a : ℝ) (hβ : 0 < β) :
    Tendsto (fun M : ℝ => 3*h*a/M + 2*hotProbability β M*a) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun M : ℝ => 3*h*a/M) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (3*h*a)
  have hsecond := ((hotProbability_tendsto_zero β hβ).const_mul 2).mul_const a
  simpa only [mul_zero, zero_mul, add_zero] using hfirst.add hsecond

theorem hot_gap_parameters (β h a η : ℝ) (hβ : 0 < β) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ 2*a ≤ M ∧ 3*h*a/M + 2*hotProbability β M*a ≤ η := by
  have hr : ∀ᶠ M : ℝ in atTop, 3*h*a/M + 2*hotProbability β M*a < η :=
    (tendsto_order.mp (hot_remainder_tendsto_zero β h a hβ)).2 η hη
  obtain ⟨M,hM,hrem⟩ := ((eventually_gt_atTop (max 0 (2*a))).and hr).exists
  exact ⟨M,(le_max_left _ _).trans_lt hM,(le_max_right _ _).trans hM.le,hrem.le⟩

def hotContact {d : ℕ} (D : Mat (Fin d)) (M : ℝ) : Mat (Fin d ⊕ Fin d) :=
  fromBlocks (matrixSqrt (1-((M⁻¹ : ℝ) : ℂ) • D))
    (-matrixSqrt (((M⁻¹ : ℝ) : ℂ) • D))
    (matrixSqrt (((M⁻¹ : ℝ) : ℂ) • D)) (matrixSqrt (1-((M⁻¹ : ℝ) : ℂ) • D))

def hotInput {d : ℕ} (ρ : Mat (Fin d)) (β M : ℝ) : Mat (Fin d ⊕ Fin d) :=
  fromBlocks (((1-hotProbability β M : ℝ) : ℂ) • ρ) 0 0
    (((hotProbability β M : ℝ) : ℂ) • ρ)

theorem heat_trace_blocks {d : ℕ} (A B C E : Mat (Fin d)) :
    (fromBlocks A B C E).trace = A.trace + E.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem hot_energy_readout {d : ℕ} (M : ℝ) (X : Mat (Fin d ⊕ Fin d)) :
    energy (fromBlocks 0 0 0 ((M : ℂ) • (1 : Mat (Fin d)))) X =
      M * X.toBlocks₂₂.trace.re := by
  unfold energy
  conv_lhs => rw [← fromBlocks_toBlocks X]
  rw [fromBlocks_multiply]
  simp only [zero_mul, zero_add, smul_mul_assoc, one_mul, heat_trace_blocks,
    trace_zero, trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem heat_effect_unitary {d : ℕ} (D : Mat (Fin d)) (hD : D.PosSemidef)
    (M : ℝ) (hM : 0 < M) (hbig : 2*‖D‖ ≤ M) : IsUnitary (hotContact D M) := by
  obtain ⟨ha,hb,he,hn,hbn⟩ := hot_effect_properties D hD M hM hbig
  let A := ((M⁻¹ : ℝ) : ℂ) • D
  let C := matrixSqrt (1-A)
  let F := matrixSqrt A
  have hc : C.IsHermitian := matrixSqrt_hermitian (1-A) hb.isHermitian
  have hf : F.IsHermitian := matrixSqrt_hermitian A ha.isHermitian
  have hcc : C*C = 1-A := matrixSqrt_mul_self (1-A) hb
  have hff : F*F = A := matrixSqrt_mul_self A ha
  have hcf : C*F = F*C := by
    apply matrixSqrt_commute (1-A) A hb.isHermitian ha.isHermitian
    change (1-A)*A = A*(1-A)
    noncomm_ring
  change IsUnitary (fromBlocks C (-F) F C)
  constructor <;>
    simp only [fromBlocks_conjTranspose, conjTranspose_neg, hc.eq, hf.eq,
      fromBlocks_multiply, neg_mul, mul_neg, neg_neg, hcf, neg_add_cancel,
      add_neg_cancel, hcc, hff, sub_add_cancel, add_sub_cancel,
      fromBlocks_one]

theorem heat_effect_gain {d : ℕ} (β M : ℝ) (hM : 0 < M)
    (D : Mat (Fin d)) (hD : D.PosSemidef) (hbig : 2*‖D‖ ≤ M) (ρ : Density (Fin d)) :
    energy (fromBlocks 0 0 0 (((M : ℂ)) • (1 : Mat (Fin d))))
      (evolve (hotContact D M) (hotInput ρ.matrix β M)-hotInput ρ.matrix β M) =
        (1-2*hotProbability β M)*energy D ρ.matrix := by
  obtain ⟨ha,hb,he,hn,hbn⟩ := hot_effect_properties D hD M hM hbig
  let A := ((M⁻¹ : ℝ) : ℂ) • D
  let C := matrixSqrt (1-A)
  let F := matrixSqrt A
  let p := hotProbability β M
  have hc : C.IsHermitian := matrixSqrt_hermitian (1-A) hb.isHermitian
  have hf : F.IsHermitian := matrixSqrt_hermitian A ha.isHermitian
  have hcc : C*C = 1-A := matrixSqrt_mul_self (1-A) hb
  have hff : F*F = A := matrixSqrt_mul_self A ha
  have hout : (evolve (hotContact D M) (hotInput ρ.matrix β M)).toBlocks₂₂ =
      ((1-p : ℝ) : ℂ) • (F*ρ.matrix*F) + (p : ℂ) • (C*ρ.matrix*C) := by
    change (fromBlocks C (-F) F C *
      fromBlocks (((1-p : ℝ) : ℂ) • ρ.matrix) 0 0 ((p : ℂ) • ρ.matrix) *
        (fromBlocks C (-F) F C)ᴴ).toBlocks₂₂ = _
    simp only [fromBlocks_conjTranspose, conjTranspose_neg, hc.eq, hf.eq,
      fromBlocks_multiply, toBlocks_fromBlocks₂₂, mul_zero, zero_mul,
      add_zero, zero_add, mul_smul_comm, smul_mul_assoc]
  have htF : (F*ρ.matrix*F).trace = ((M⁻¹ : ℝ) : ℂ) * (D*ρ.matrix).trace := by
    rw [trace_mul_cycle, hff]
    simp only [A, smul_mul_assoc, trace_smul, smul_eq_mul]
  have htC : (C*ρ.matrix*C).trace =
      ρ.matrix.trace - ((M⁻¹ : ℝ) : ℂ) * (D*ρ.matrix).trace := by
    rw [trace_mul_cycle, hcc, sub_mul, one_mul, trace_sub]
    simp only [A, smul_mul_assoc, trace_smul, smul_eq_mul]
  have hsub (H X Y : Mat (Fin d ⊕ Fin d)) : energy H (X-Y) = energy H X - energy H Y := by
    simp only [energy, mul_sub, trace_sub, Complex.sub_re]
  rw [hsub, hot_energy_readout, hot_energy_readout, hout]
  simp only [hotInput, toBlocks_fromBlocks₂₂, trace_add, trace_smul, smul_eq_mul,
    htF, htC, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, energy]
  change M * ((1-p) * (M⁻¹ * (D*ρ.matrix).trace.re) +
    p * (ρ.matrix.trace.re - M⁻¹ * (D*ρ.matrix).trace.re)) -
      M * (p * ρ.matrix.trace.re) = (1-2*p) * (D*ρ.matrix).trace.re
  field_simp [hM.ne']; ring

theorem heat_effect_disturbance {d : ℕ} (D Q : Mat (Fin d)) (hD : D.PosSemidef)
    (hQ : Q.IsHermitian) (M : ℝ) (hM : 0 < M) (hbig : 2*‖D‖ ≤ M) :
    let C := matrixSqrt (1-((M⁻¹ : ℝ) : ℂ) • D)
    let F := matrixSqrt (((M⁻¹ : ℝ) : ℂ) • D)
    ‖C*Q*C+F*Q*F-Q‖ ≤ 3*‖Q‖*‖D‖/M := by
  obtain ⟨ha,hb,he,hn,hbn⟩ := hot_effect_properties D hD M hM hbig
  let A := ((M⁻¹ : ℝ) : ℂ) • D
  let C := matrixSqrt (1-A)
  let F := matrixSqrt A
  have hc1 : ‖C‖ ≤ 1 := matrixSqrt_norm_le_one (1-A) hb.isHermitian hbn
  have hcm : ‖C-1‖ ≤ ‖A‖ := by
    have hv : (1-A)-1 = -A := by abel
    simpa only [hv, norm_neg] using matrixSqrt_sub_one_norm (1-A) hb hbn
  have hf : F.IsHermitian := matrixSqrt_hermitian A ha.isHermitian
  have hf2 : ‖F‖*‖F‖ = ‖A‖ := by
    calc ‖F‖*‖F‖ = ‖Fᴴ*F‖ := CStarRing.norm_star_mul_self.symm
         _ = ‖A‖ := by rw [hf.eq, matrixSqrt_mul_self A ha]
  have hleft : ‖(C-1)*Q*C‖ ≤ ‖A‖*‖Q‖ := by
    calc ‖(C-1)*Q*C‖ ≤ (‖C-1‖*‖Q‖)*‖C‖ :=
           (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
         _ ≤ (‖A‖*‖Q‖)*1 := mul_le_mul
           (mul_le_mul_of_nonneg_right hcm (norm_nonneg Q)) hc1
           (norm_nonneg C) (mul_nonneg (norm_nonneg A) (norm_nonneg Q))
         _ = ‖A‖*‖Q‖ := mul_one _
  have hright : ‖Q*(C-1)‖ ≤ ‖Q‖*‖A‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hcm (norm_nonneg _))
  have hbranch : ‖F*Q*F‖ ≤ ‖Q‖*‖A‖ := by
    calc ‖F*Q*F‖ ≤ (‖F‖*‖Q‖)*‖F‖ :=
           (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
         _ = ‖Q‖*(‖F‖*‖F‖) := by ring
         _ = ‖Q‖*‖A‖ := by rw [hf2]
  change ‖C*Q*C+F*Q*F-Q‖ ≤ _
  calc ‖C*Q*C+F*Q*F-Q‖ = ‖(C-1)*Q*C+Q*(C-1)+F*Q*F‖ := by
         congr 1
         noncomm_ring
       _ ≤ (‖(C-1)*Q*C‖+‖Q*(C-1)‖)+‖F*Q*F‖ :=
         (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
       _ ≤ (‖A‖*‖Q‖+‖Q‖*‖A‖)+‖Q‖*‖A‖ := add_le_add (add_le_add hleft hright) hbranch
       _ = 3*‖Q‖*‖D‖/M := by rw [he]; ring

theorem hot_probability_bounds (β M : ℝ) : 0 < hotProbability β M ∧ hotProbability β M < 1 := by
  have hx := Real.exp_pos (β*M)
  unfold hotProbability
  constructor
  · positivity
  · rw [inv_lt_one₀ (by linarith : 0 < 1+Real.exp (β*M))]
    linarith

theorem hot_probability_log_gap (β M : ℝ) :
    Real.log (1-hotProbability β M)-Real.log (hotProbability β M) = β*M := by
  have hx := Real.exp_pos (β*M)
  have hd : 0 < 1+Real.exp (β*M) := by linarith
  have he : 1-hotProbability β M = Real.exp (β*M)/(1+Real.exp (β*M)) := by
    unfold hotProbability
    field_simp
    ring
  rw [he,Real.log_div (Real.exp_ne_zero _) hd.ne',Real.log_exp,hotProbability,Real.log_inv]
  ring

theorem heat_body_response {d : ℕ} (β M : ℝ) (hM : 0 < M)
    (D Q ρ : Mat (Fin d)) (hD : D.PosSemidef) (hbig : 2*‖D‖ ≤ M) :
    let C := matrixSqrt (1-((M⁻¹ : ℝ) : ℂ) • D)
    let F := matrixSqrt (((M⁻¹ : ℝ) : ℂ) • D)
    energy (ClassicalFlag.block Q Q) (evolve (hotContact D M) (hotInput ρ β M)) =
      energy (C*Q*C+F*Q*F) ρ := by
  obtain ⟨ha,hb,_,_,_⟩ := hot_effect_properties D hD M hM hbig
  exact rotatedFlag_body_energy Q _ _ ρ (matrixSqrt_hermitian _ hb.isHermitian)
    (matrixSqrt_hermitian _ ha.isHermitian) (hotProbability β M)

theorem hot_input_body_energy {d : ℕ} (β M : ℝ) (Q ρ : Mat (Fin d)) :
    energy (ClassicalFlag.block Q Q) (hotInput ρ β M) = energy Q ρ := by
  change energy (ClassicalFlag.block Q Q) (ClassicalFlag.block _ _) = _
  rw [energy_blocks,ClassicalFlag.energy_weight,ClassicalFlag.energy_weight]
  ring

theorem hot_input_heat_energy {d : ℕ} (β M : ℝ) (ρ : Density (Fin d)) :
    energy (fromBlocks 0 0 0 ((M : ℂ) • (1 : Mat (Fin d)))) (hotInput ρ.matrix β M) =
      M*hotProbability β M := by
  rw [hot_energy_readout]
  simp [hotInput,trace_smul,ρ.normalized]

theorem heat_energy_sub {a : Type} [Fintype a] (H X Y : Mat a) :
    energy H (X-Y) = energy H X-energy H Y := by
  simp [energy,mul_sub,trace_sub]

theorem heat_initialized_bound {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (q : Density (Fin e.b)) (hq : q.matrix.PosDef)
    (D : Mat (Fin e.b)) (hD : D.PosSemidef) (M : ℝ) (hM : 0 < M) (hbig : 2*‖D‖ ≤ M)
    (w : ℝ) (hslack : ∀ r (t : Tester S r), energy D (bodyOutput e t) = w-physicalLinearized β e q t) :
    let p := hotProbability β M
    let hp := (hot_probability_bounds β M).1
    let hp1 := (hot_probability_bounds β M).2
    ∀ r (t : Tester S r),
      |physicalLinearized β
        (thermalBodyContact e p hp hp1 (hotContact D M) (heat_effect_unitary D hD M hM hbig))
        (flagReference q hq p hp hp1) t-w| ≤
          3*‖tangentHamiltonian β q‖*‖D‖/M+2*p*‖D‖ := by
  dsimp only
  intro r t
  let p := hotProbability β M
  let Q := tangentHamiltonian β q
  let C := matrixSqrt (1-((M⁻¹ : ℝ) : ℂ) • D)
  let F := matrixSqrt (((M⁻¹ : ℝ) : ℂ) • D)
  let B := ClassicalFlag.block Q Q
  let H : Mat (Fin e.b ⊕ Fin e.b) := fromBlocks 0 0 0 ((M : ℂ) • (1 : Mat (Fin e.b)))
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  let R := C*Q*C+F*Q*F-Q-((2*p : ℝ) : ℂ) • D
  have hb : energy B (evolve (hotContact D M) (hotInput ρ.matrix β M)) = energy (C*Q*C+F*Q*F) ρ.matrix :=
    heat_body_response β M hM D Q ρ.matrix hD hbig
  have hh : energy H (evolve (hotContact D M) (hotInput ρ.matrix β M)-hotInput e.source.matrix β M) =
      (1-2*p)*energy D ρ.matrix := by
    have h := heat_effect_gain β M hM D hD hbig ρ
    rw [heat_energy_sub,hot_input_heat_energy] at h ⊢
    exact h
  have hR : energy R ρ.matrix = energy (C*Q*C+F*Q*F) ρ.matrix - energy Q ρ.matrix -
      2*p*energy D ρ.matrix := by
    dsimp [R]
    simp only [energy,sub_mul,trace_sub,Complex.sub_re,smul_mul_assoc,trace_smul]
    simp
  have heq : physicalLinearized β
      (thermalBodyContact e p (hot_probability_bounds β M).1 (hot_probability_bounds β M).2
        (hotContact D M) (heat_effect_unitary D hD M hM hbig))
      (flagReference q hq p (hot_probability_bounds β M).1 (hot_probability_bounds β M).2) t-w =
        energy R ρ.matrix := by
    rw [thermalBodyContact_linearized β hβ.ne' e q hq p _ _ M (hot_probability_log_gap β M)]
    change handoff e t+energy (B+H) (evolve (hotContact D M) (hotInput ρ.matrix β M)-hotInput e.source.matrix β M)-w = _
    have hi : energy B (hotInput e.source.matrix β M) = energy Q e.source.matrix :=
      hot_input_body_energy β M Q e.source.matrix
    rw [energy_add,hh,heat_energy_sub,hb,hi,hR]
    have hs := hslack r t
    unfold physicalLinearized at hs
    rw [heat_energy_sub Q] at hs
    change energy D ρ.matrix = w-(handoff e t+(energy Q ρ.matrix-energy Q e.source.matrix)) at hs
    linarith
  rw [heq]
  have hn : ‖R‖ ≤ 3*‖Q‖*‖D‖/M+2*p*‖D‖ := by
    have hp : 0 ≤ 2*p := mul_nonneg (by norm_num) (hot_probability_bounds β M).1.le
    calc ‖R‖ ≤ ‖C*Q*C+F*Q*F-Q‖+‖((2*p : ℝ) : ℂ) • D‖ := norm_sub_le _ _
         _ ≤ 3*‖Q‖*‖D‖/M+2*p*‖D‖ := by
           rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
           exact add_le_add (heat_effect_disturbance D Q hD (tangentHamiltonian_hermitian β q) M hM hbig) le_rfl
  exact (density_energy_abs_le R ρ).trans hn

theorem physical_slack_effect {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (h : 0 < S.visits) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : Density (Fin (Recorder.rare e δ hδ.le hδ1).b)) (hq : q.matrix.PosDef) (w a : ℝ)
    (hmax : ∀ r (t : Tester S r), physicalLinearized β (Recorder.rare e δ hδ.le hδ1) q t ≤ w)
    (hup : sourceFreeTerm β (Recorder.rare e δ hδ.le hδ1) q+w ≤
      scoreBound β (Recorder.rare e δ hδ.le hδ1)+a) :
    ∃ D : Mat (Fin (Recorder.rare e δ hδ.le hδ1).b), D.PosSemidef ∧
      ‖D‖ ≤ (prefixDimension (lastInputBurst S h) : ℝ)*(terminalInputDimension S h : ℝ)*
        (2*scoreBound β (Recorder.rare e δ hδ.le hδ1)+a)/δ ∧
      ∀ r (t : Tester S r), energy D (partialRight (run (Recorder.rare e δ hδ.le hδ1) t
        (recordTime (lastInputBurst S h)))) = w-physicalLinearized β (Recorder.rare e δ hδ.le hδ1) q t := by
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
    rw [he,hJ]

theorem initialized_heat_plan_zero_visits {I : Inventory} {S : Schedule I}
    (β : ℝ) (hβ : 0 < β) (e : Extension S) (hz : S.visits = 0)
    (g : ℝ) (hg : ∀ r (t : Tester S r), score β e t ≤ g)
    (η : ℝ) (hη : 0 < η) : Nonempty (InitializedPlan β e g η) := by
  let z : Mat (Fin e.b) × ℝ := (zeroVisitBody e, 0)
  let K : Set (Mat (Fin e.b) × ℝ) := {z}
  have hρ : SectionDensities e.b K := by
    intro x hx
    have hxz : x=z := Set.mem_singleton_iff.mp hx
    subst x
    exact zero_visit_body_density e hz
  have hscore : ∀ x ∈ K, (entropy x.1-entropy e.source.matrix)/β+x.2 ≤ g := by
    intro x hx
    have hxz : x=z := Set.mem_singleton_iff.mp hx
    subst x
    simpa only [z, zero_visit_score_constant β e hz, add_zero] using hg 1 (idleTester S)
  let s := 1-Real.exp (-β*η)
  have hs : 0 < s := by
    dsimp [s]
    have he : Real.exp (-β*η) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [Real.exp_pos (-β*η)]
  have hlog : Real.log (1-s) = -β*η := by
    rw [show 1-s = Real.exp (-β*η) by dsimp [s]; ring, Real.log_exp]
  have hslack : g-Real.log (1-s)/β = g+η := by rw [hlog]; field_simp [hβ.ne']; ring
  obtain ⟨q,hq,hbound⟩ := section_joint_reference e.b_pos β hβ K
    isCompact_singleton (convex_singleton z) (Set.singleton_nonempty z) hρ e.source g hscore s hs hs1
  have hzK : z ∈ K := Set.mem_singleton z
  have hpoint := hbound z hzK
  rw [hslack] at hpoint
  let w := physicalLinearized β e q (idleTester S)
  refine ⟨{
    bare := e
    reference := q
    faithful := hq
    w := w
    residual := 0
    residual_nonneg := le_rfl
    residual_small := hη.le
    service := ?_
    rate := ?_
    initialized := ?_ }⟩
  · intro r t
    simpa only [traceDistance, sub_self, ClassicalFlag.traceNorm_eq_library,
      Matrix.traceNorm_zero, zero_div] using hη.le
  · change sourceFreeTerm β e q + physicalLinearized β e q (idleTester S) ≤ g+η
    rw [physical_score_tangent_identity]
    unfold score faithfulRelativeEntropy
    rw [bodyOutput_zero_visits e hz, handoff_zero_visits e hz]
    have he : energy (matrixLog q.matrix) (zeroVisitBody e) =
        (zeroVisitBody e * matrixLog q.matrix).trace.re :=
      congrArg Complex.re (trace_mul_comm _ _)
    dsimp only [z] at hpoint
    rw [he] at hpoint
    convert hpoint using 1 <;> ring
  · intro r t
    have heq : physicalLinearized β e q t = w := by
      dsimp [w, physicalLinearized]
      rw [bodyOutput_zero_visits e hz, bodyOutput_zero_visits e hz,
        handoff_zero_visits e hz, handoff_zero_visits e hz]
    rw [heq, sub_self, abs_zero]

/-- Parameter selection, rare-flag service, physical slack, initialized hot
qubit and its complete remainder; includes the zero-visit branch. -/
theorem initialized_heat_plan {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g : ℝ) (hg : ∀ r (t : Tester S r), score β e t ≤ g)
    (η : ℝ) (hη : 0 < η) : Nonempty (InitializedPlan β e g η) := by
  by_cases hz : S.visits = 0
  · exact initialized_heat_plan_zero_visits β hβ e hz g hg η hη
  have h : 0 < S.visits := Nat.pos_of_ne_zero hz
  let ν := η/4
  have hν : 0 < ν := by dsimp [ν]; positivity
  obtain ⟨δ,hδ,hδ1,hservice,hscore,_⟩ := Recorder.small_rare_branch β hβ e g hg ν hν
  let er := Recorder.rare e δ hδ.le hδ1
  let s := 1-Real.exp (-β*ν)
  have hs : 0 < s := by
    dsimp [s]
    have he : Real.exp (-β*ν) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [Real.exp_pos (-β*ν)]
  have hlog : Real.log (1-s) = -β*ν := by
    rw [show 1-s = Real.exp (-β*ν) by dsimp [s]; ring,Real.log_exp]
  have hrate : g+ν-Real.log (1-s)/β = g+2*ν := by rw [hlog]; field_simp [hβ.ne']; ring
  obtain ⟨q,hq,w,hmax,_,hw⟩ := joint_tangent β hβ er (g+ν) hscore s hs hs1
  rw [hrate] at hw
  obtain ⟨D,hD,_,he⟩ := physical_slack_effect_final β hβ e h δ hδ hδ1 q hq w
    (sourceFreeTerm β er q+w-scoreBound β er) (hmax) (by dsimp [er]; linarith)
  obtain ⟨M,hM,hbig,hrem⟩ := hot_gap_parameters β ‖tangentHamiltonian β q‖ ‖D‖ η hβ hη
  let p := hotProbability β M
  have hp := (hot_probability_bounds β M).1
  have hp1 := (hot_probability_bounds β M).2
  let u := hotContact D M
  have hu : IsUnitary u := heat_effect_unitary D hD M hM hbig
  let bare := thermalBodyContact er p hp hp1 u hu
  let reference := flagReference q hq p hp hp1
  refine ⟨{
    bare := bare
    reference := reference
    faithful := flagReference_faithful q hq p hp hp1
    w := w
    residual := 3*‖tangentHamiltonian β q‖*‖D‖/M+2*p*‖D‖
    residual_nonneg := by positivity
    residual_small := hrem
    service := ?_
    rate := ?_
    initialized := heat_initialized_bound β hβ er q hq D hD M hM hbig w he }⟩
  · intro r t
    change traceDistance (observerOutput (thermalBodyContact er p hp hp1 u hu) t) (observerOutput e t) ≤ η
    rw [thermalBodyContact_observerOutput]
    exact (hservice r t).trans (by dsimp [ν]; linarith)
  · change sourceFreeTerm β (thermalBodyContact er p hp hp1 u hu) (flagReference q hq p hp hp1)+w ≤ g+η
    rw [thermalBodyContact_sourceFreeTerm]
    exact hw.trans (by dsimp [ν]; linarith)

end ScheduleLaw.Blueprint
