/-
Copyright (c) 2026 QuAIR. Released under Apache 2.0 license.
Authors of reused spectral row/column normalization proofs: QuAIR Team.
Adapted spectral/Jensen argument; all state, entropy, matrix and distance
interfaces below are the original ScheduleLaw definitions under Lean 4.30.
-/
/- Finite natural-log Fannes bridge. The scalar modulus is adapted with
provenance in FiniteFannesScalar. The spectral/Jensen route follows the
companion Fannes proof, but uses only the original ScheduleLaw Density,
entropy and half-trace-distance definitions and the pinned 4.30 libraries. -/
import FiniteFannesScalar
import FactoryBattery
import FiniteTensorMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FiniteFannes
open History
variable {a : Type} [Fintype a] [DecidableEq a]

theorem row_norm (U : Matrix.unitaryGroup a ℂ) (i : a) : ∑ j,Complex.normSq ((U : Mat a) i j)=1 := by
  have hunit : (U : Mat a)*star (U : Mat a)=1 := Unitary.coe_mul_star_self U
  have h := congrArg Complex.re (congrFun (congrFun hunit i) i)
  simpa [Matrix.mul_apply,Matrix.one_apply,Complex.normSq_eq_conj_mul_self,
    Complex.normSq_apply,mul_comm] using h

theorem col_norm (U : Matrix.unitaryGroup a ℂ) (j : a) : ∑ i,Complex.normSq ((U : Mat a) i j)=1 := by
  have hunit : star (U : Mat a)*(U : Mat a)=1 := Unitary.coe_star_mul_self U
  have h := congrArg Complex.re (congrFun (congrFun hunit j) j)
  simpa [Matrix.mul_apply,Matrix.one_apply,Complex.normSq_eq_conj_mul_self,
    Complex.normSq_apply,mul_comm] using h

theorem diagonal_spectral (B : Mat a) (hB : B.IsHermitian) (i : a) :
    (B i i).re=∑ j,hB.eigenvalues j*Complex.normSq ((hB.eigenvectorUnitary : Mat a) i j) := by
  let U : Matrix.unitaryGroup a ℂ := hB.eigenvectorUnitary
  let D : Mat a := diagonal (fun j => (hB.eigenvalues j : ℂ))
  have he : B=(U : Mat a)*D*(U : Mat a)ᴴ := hB.spectral_theorem
  have h := congrArg Complex.re (congrFun (congrFun he i) i)
  simpa [U,D,Matrix.mul_apply,Matrix.diagonal,Complex.normSq_eq_conj_mul_self,
    Complex.normSq_apply,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h

theorem diagonal_traceNorm (B : Mat a) (hB : B.IsHermitian) :
    (∑ i,|(B i i).re|)≤Matrix.traceNorm B := by
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hB]
  calc _ = ∑ i,|∑ j,hB.eigenvalues j*Complex.normSq ((hB.eigenvectorUnitary : Mat a) i j)| := by
         simp_rw [diagonal_spectral B hB]
       _ ≤ ∑ i,∑ j,|hB.eigenvalues j| *Complex.normSq ((hB.eigenvectorUnitary : Mat a) i j) := by
         apply Finset.sum_le_sum
         intro i _
         calc _ ≤ ∑ j,|hB.eigenvalues j*Complex.normSq ((hB.eigenvectorUnitary : Mat a) i j)| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = _ := by simp only [abs_mul,abs_of_nonneg (Complex.normSq_nonneg _)]
       _ = _ := by
         rw [Finset.sum_comm]
         apply Finset.sum_congr rfl
         intro j _
         rw [← Finset.mul_sum,col_norm,mul_one]
         rfl

def conjugate (ρ : Density a) (U : Matrix.unitaryGroup a ℂ) : Density a :=
  ⟨evolve (star U : Mat a) ρ.matrix,
    (evolve_density _ _ (star U).property ρ.positive ρ.normalized).1,
    (evolve_density _ _ (star U).property ρ.positive ρ.normalized).2⟩

theorem entropy_diagonal (ρ : Density a) (U : Matrix.unitaryGroup a ℂ) :
    entropy ρ.matrix≤∑ i,Real.negMulLog ((conjugate ρ U).matrix i i).re := by
  let B := conjugate ρ U
  have he : entropy B.matrix=entropy ρ.matrix :=
    entropy_unitary_evolve (star U : Mat a) ρ.matrix (star U).property ρ.positive
  rw [← he,entropy_of_hermitian _ B.positive.isHermitian]
  let H := B.positive.isHermitian
  have hi (i : a) : (∑ j,Complex.normSq ((H.eigenvectorUnitary : Mat a) i j)*
      Real.negMulLog (H.eigenvalues j)) ≤ Real.negMulLog (B.matrix i i).re := by
    have hw : ∑ j ∈ (Finset.univ : Finset a),Complex.normSq ((H.eigenvectorUnitary : Mat a) i j)=1 := by
      simpa using row_norm H.eigenvectorUnitary i
    have hj := Real.concaveOn_negMulLog.le_map_sum (t:=Finset.univ)
      (w:=fun j => Complex.normSq ((H.eigenvectorUnitary : Mat a) i j)) (p:=H.eigenvalues)
      (fun j _ => Complex.normSq_nonneg _) hw (fun j _ => B.positive.eigenvalues_nonneg j)
    calc _ ≤ Real.negMulLog (∑ j,Complex.normSq ((H.eigenvectorUnitary : Mat a) i j)*H.eigenvalues j) := by
           simpa only [Finset.mem_univ,Function.comp_apply,smul_eq_mul] using hj
         _ = _ := by
           rw [diagonal_spectral B.matrix H]
           congr 1
           apply Finset.sum_congr rfl
           intro j _
           ring
  calc _ = ∑ i,∑ j,Complex.normSq ((H.eigenvectorUnitary : Mat a) i j)*Real.negMulLog (H.eigenvalues j) := by
         symm
         rw [Finset.sum_comm]
         apply Finset.sum_congr rfl
         intro j _
         rw [← Finset.sum_mul,col_norm,one_mul]
       _ ≤ _ := Finset.sum_le_sum (fun i _ => hi i)

theorem eigenbasis (σ : Density a) :
    (conjugate σ σ.positive.isHermitian.eigenvectorUnitary).matrix =
      diagonal (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ)) := by
  let U := σ.positive.isHermitian.eigenvectorUnitary
  have hs : σ.matrix=evolve (U : Mat a) (diagonal (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ))) :=
    σ.positive.isHermitian.spectral_theorem
  change evolve (star U : Mat a) σ.matrix=_
  conv_lhs => arg 2; rw [hs]
  rw [← evolve_mul]
  have hu : (star U : Mat a)*(U : Mat a)=1 := Unitary.coe_star_mul_self U
  rw [hu]
  simp only [evolve,conjTranspose_one,one_mul,mul_one]

theorem diagonal_difference (ρ σ : Density a) (U : Matrix.unitaryGroup a ℂ) :
    (∑ i,|((conjugate ρ U).matrix i i).re-((conjugate σ U).matrix i i).re|) ≤
      Matrix.traceNorm (ρ.matrix-σ.matrix) := by
  let B : Mat a := evolve (star U : Mat a) (ρ.matrix-σ.matrix)
  have hB : B.IsHermitian := isHermitian_mul_mul_conjTranspose (star U : Mat a)
    (ρ.positive.isHermitian.sub σ.positive.isHermitian)
  have he : B=(conjugate ρ U).matrix-(conjugate σ U).matrix := by
    simp only [B,conjugate,evolve,mul_sub,sub_mul]
  have hn : Matrix.traceNorm B=Matrix.traceNorm (ρ.matrix-σ.matrix) := by
    have hd := FiniteResidue.traceDistance_unitary (star U : Mat a) (ρ.matrix-σ.matrix) 0 (star U).property
    have hz : evolve (star U : Mat a) 0=0 := by simp [evolve]
    rw [hz] at hd
    unfold traceDistance at hd
    rw [ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library] at hd
    simp only [sub_zero] at hd
    change Matrix.traceNorm B/2=Matrix.traceNorm (ρ.matrix-σ.matrix)/2 at hd
    linarith
  calc _ = ∑ i,|(B i i).re| := by simp only [he,Matrix.sub_apply,Complex.sub_re]
       _ ≤ Matrix.traceNorm B := diagonal_traceNorm B hB
       _ = _ := hn

theorem entropy_sub_bound (ρ σ : Density a) :
    entropy ρ.matrix-entropy σ.matrix≤
      Matrix.traceNorm (ρ.matrix-σ.matrix)*Real.log (Fintype.card a : ℝ)+
        FiniteFannesScalar.correction (Matrix.traceNorm (ρ.matrix-σ.matrix)) := by
  letI : Nonempty a := σ.toMState.nonempty
  let U := σ.positive.isHermitian.eigenvectorUnitary
  let p (i : a) := ((conjugate ρ U).matrix i i).re
  let q (i : a) := σ.positive.isHermitian.eigenvalues i
  have hp0 (i : a) : 0≤p i := FactoryBattery.diagonal_nonneg (conjugate ρ U) i
  have hpS : ∑ i,p i=1 := FactoryBattery.diagonal_sum (conjugate ρ U)
  have hp1 (i : a) : p i≤1 := by
    calc p i ≤ ∑ j,p j := Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
         _ = 1 := hpS
  have hq0 (i : a) : 0≤q i := σ.positive.eigenvalues_nonneg i
  have hqS : ∑ i,q i=1 := density_eigenvalues_sum σ
  have hq1 (i : a) : q i≤1 := by
    calc q i ≤ ∑ j,q j := Finset.single_le_sum (fun j _ => hq0 j) (Finset.mem_univ i)
         _ = 1 := hqS
  have hqdiag (i : a) : q i=((conjugate σ U).matrix i i).re := by
    rw [show (conjugate σ U).matrix=diagonal (fun i => (q i : ℂ)) from eigenbasis σ]
    simp
  have hd : (∑ i,|p i-q i|)≤Matrix.traceNorm (ρ.matrix-σ.matrix) := by
    simpa only [p,hqdiag] using diagonal_difference ρ σ U
  have hb := FiniteFannesScalar.classical_entropy_additive p q hp0 hp1 hq0 hq1
  change |(∑ i,Real.negMulLog (p i))-(∑ i,Real.negMulLog (q i))| ≤
    (∑ i,|p i-q i|)*Real.log (Fintype.card a : ℝ)+FiniteFannesScalar.correction (∑ i,|p i-q i|) at hb
  have hl : 0≤Real.log (Fintype.card a : ℝ) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=a))
  have hσ : entropy σ.matrix=∑ i,Real.negMulLog (q i) := entropy_of_hermitian _ σ.positive.isHermitian
  calc _ ≤ (∑ i,Real.negMulLog (p i))-(∑ i,Real.negMulLog (q i)) := by
         rw [hσ]
         exact sub_le_sub_right (entropy_diagonal ρ U) _
       _ ≤ |(∑ i,Real.negMulLog (p i))-(∑ i,Real.negMulLog (q i))| := le_abs_self _
       _ ≤ _ := hb
       _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hd hl)
         (FiniteFannesScalar.correction_mono (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hd)

theorem entropy_bound (ρ σ : Density a) :
    |entropy ρ.matrix-entropy σ.matrix|≤
      Matrix.traceNorm (ρ.matrix-σ.matrix)*Real.log (Fintype.card a : ℝ)+
        FiniteFannesScalar.correction (Matrix.traceNorm (ρ.matrix-σ.matrix)) := by
  have hf := entropy_sub_bound ρ σ
  have hb := entropy_sub_bound σ ρ
  have he : σ.matrix-ρ.matrix= -(ρ.matrix-σ.matrix) := by abel
  rw [he,Matrix.traceNorm_neg] at hb
  rw [abs_le]
  constructor <;> linarith

/-- Faithful to the original half-trace-distance and natural-log entropy. -/
theorem trace_distance_bound (ρ σ : Density a) :
    |entropy ρ.matrix-entropy σ.matrix|≤
      2*traceDistance ρ.matrix σ.matrix*Real.log (Fintype.card a : ℝ)+
        FiniteFannesScalar.correction (2*traceDistance ρ.matrix σ.matrix) := by
  have h := entropy_bound ρ σ
  have he : Matrix.traceNorm (ρ.matrix-σ.matrix)=2*traceDistance ρ.matrix σ.matrix := by
    rw [traceDistance,ClassicalFlag.traceNorm_eq_library]
    ring
  simpa only [he] using h

end ScheduleLaw.Blueprint.FiniteFannes
