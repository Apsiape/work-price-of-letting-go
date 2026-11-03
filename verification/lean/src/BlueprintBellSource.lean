import BlueprintFirstInitialization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

/-- All Bell pairs are unnormalized during the amplitude induction. -/
def allBellSource {I : Inventory} (S : Schedule I) (x : Recorder.Stock S) : ℂ :=
  if x.1=x.2 then 1 else 0

theorem allBellSource_scale {I : Inventory} (S : Schedule I) :
    allBellSource S=(Real.sqrt (Fintype.card (Recorder.Inputs S):ℝ):ℂ) •
      (Recorder.epr (a := Recorder.Inputs S)) := by
  have hp : (0:ℝ)<Fintype.card (Recorder.Inputs S) := by exact_mod_cast Fintype.card_pos
  have hz : (Real.sqrt (Fintype.card (Recorder.Inputs S):ℝ):ℂ)≠0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hp)
  funext x
  by_cases h : x.1=x.2
  · simp only [allBellSource,Recorder.epr,if_pos h,Pi.smul_apply,smul_eq_mul,Complex.ofReal_inv]
    exact (mul_inv_cancel₀ hz).symm
  · simp [allBellSource,Recorder.epr,h]

def allBellGram {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (n : ℕ) (A O : Finset (Fin S.visits)) : Mat (Record S A O) :=
  partialRight (pureMatrix (fun x => amplitudes t (allBellSource S) n
    ((recordCoordinates S r A O).symm x)))

theorem allBellGram_physical {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (n : ℕ) (A O : Finset (Fin S.visits)) :
    allBellGram t n A O=(Fintype.card (Recorder.Inputs S):ℂ) • chi t n A O := by
  have he : (fun x => amplitudes t (allBellSource S) n ((recordCoordinates S r A O).symm x)) =
      (Real.sqrt (Fintype.card (Recorder.Inputs S):ℝ):ℂ) •
        (fun x => amplitudes t Recorder.epr n ((recordCoordinates S r A O).symm x)) := by
    rw [allBellSource_scale,amplitudes_scale]
    rfl
  have hn : Complex.normSq (Real.sqrt (Fintype.card (Recorder.Inputs S):ℝ):ℂ)=
      (Fintype.card (Recorder.Inputs S):ℝ) := by
    rw [Complex.normSq_ofReal,Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [allBellGram,he,pureMatrix_scale,ClassicalFlag.partialRight_weight,normalized_gram_physical,hn]
  simp

theorem input_card_output_partition {I : Inventory} (S : Schedule I)
    (O : Finset (Fin S.visits)) :
    Fintype.card (Recorder.Inputs S)=outputDimension S O*Fintype.card (Registers S Oᶜ) := by
  have h := Fintype.card_congr (registerPartition S O)
  simpa only [Fintype.card_prod,registers_card] using h

/-- Normalization is paid once, at the original physical prefix readout. -/
theorem prefixGram_of_allBellGram {I : Inventory} {S : Schedule I} {r : ℕ}
    (b : InputBurst S) (t : Tester S r) (Z : Mat (PrefixSpace b))
    (h : allBellGram t (recordTime b) (arrived S (recordTime b)) (released S (recordTime b))=
      (Fintype.card (Registers S (released S (recordTime b))ᶜ):ℂ) • Z) : prefixGram b t=Z := by
  let c : ℂ := Fintype.card (Registers S (released S (recordTime b))ᶜ)
  have hc : c≠0 := by
    dsimp [c]
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0<Fintype.card (Registers S (released S (recordTime b))ᶜ)))
  have hd : (Fintype.card (Recorder.Inputs S):ℂ)=(prefixDimension b:ℂ)*c := by
    change (Fintype.card (Recorder.Inputs S):ℂ)=
      (outputDimension S (released S (recordTime b)):ℂ)*
        (Fintype.card (Registers S (released S (recordTime b))ᶜ):ℂ)
    exact_mod_cast input_card_output_partition S (released S (recordTime b))
  rw [allBellGram_physical] at h
  have he := congrArg (fun X => c⁻¹ • X) h
  change c⁻¹ • ((Fintype.card (Recorder.Inputs S):ℂ) • chi t (recordTime b)
    (arrived S (recordTime b)) (released S (recordTime b)))=c⁻¹ • (c • Z) at he
  have hs : c⁻¹*(Fintype.card (Recorder.Inputs S):ℂ)=(prefixDimension b:ℂ) := by
    rw [hd]
    field_simp
  have ht : c⁻¹*c=1 := inv_mul_cancel₀ hc
  have hh : (prefixDimension b:ℂ) • chi t (recordTime b)
      (arrived S (recordTime b)) (released S (recordTime b))=Z := by
    simpa only [smul_smul,hs,ht,one_smul] using he
  rw [prefixGram,gram_physical]
  exact hh

theorem transpose_isometry_coisometry {m z : Type} [Fintype m] [DecidableEq m]
    [Fintype z] [DecidableEq z] (J : Matrix z m ℂ) (hJ : Jᴴ*J=1) : Jᵀ*Jᵀᴴ=1 := by
  ext i j
  have h := congrFun₂ hJ i j
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    Matrix.one_apply,map_sum,star_mul,mul_comm] using congrArg star h

theorem matrix_gram_isometric_environment {a m z : Type}
    [Fintype m] [DecidableEq m] [Fintype z] [DecidableEq z]
    (P : Matrix a m ℂ) (J : Matrix z m ℂ) (hJ : Jᴴ*J=1) :
    (P*Jᵀ)*(P*Jᵀ)ᴴ=P*Pᴴ := by
  rw [conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc Jᵀ,
    transpose_isometry_coisometry J hJ,Matrix.one_mul]

theorem copied_environment_gram {a m u z : Type} [Fintype m] [DecidableEq m]
    [Fintype u] [DecidableEq u] [Fintype z] [DecidableEq z]
    (P : a × m → ℂ) (J : Matrix z (m × u) ℂ) (hJ : Jᴴ*J=1) :
    partialRight (pureMatrix (fun x : a × z => ∑ q : m × u,P (x.1,q.1)*J x.2 q)) =
      (Fintype.card u:ℂ) • partialRight (pureMatrix P) := by
  let A : Matrix a (m × u) ℂ := fun x q => P (x,q.1)
  have h := matrix_gram_isometric_environment A J hJ
  change (A*Jᵀ)*(A*Jᵀ)ᴴ=(Fintype.card u:ℂ) • partialRight (pureMatrix P)
  rw [h]
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,A,Fintype.sum_prod_type,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Matrix.smul_apply,smul_eq_mul,partialRight,pureMatrix]
  exact (Finset.mul_sum _ _ _).symm

end ScheduleLaw.Blueprint
