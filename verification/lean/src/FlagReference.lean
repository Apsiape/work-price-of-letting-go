import ActualSlackBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

/-! Exact logarithms for a retained thermal flag and a faithful body reference.
The flag weights are strictly positive; no support convention is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

def blockPairHom (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    (Mat a × Mat b) →⋆ₐ[ℂ] Mat (a ⊕ b) where
  toFun x := ClassicalFlag.block x.1 x.2
  map_zero' := by ext i j; cases i <;> cases j <;> simp [ClassicalFlag.block]
  map_one' := by simp [ClassicalFlag.block,fromBlocks_one]
  map_add' x y := by ext i j; cases i <;> cases j <;> simp [ClassicalFlag.block]
  map_mul' x y := by simp [ClassicalFlag.block,fromBlocks_multiply]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext i j; cases i <;> cases j <;> simp [ClassicalFlag.block,Matrix.one_apply]
  map_star' x := by
    change ClassicalFlag.block x.1ᴴ x.2ᴴ = (ClassicalFlag.block x.1 x.2)ᴴ
    simp [ClassicalFlag.block,fromBlocks_conjTranspose]

theorem matrixLog_eq_cfc {a : Type} [Fintype a] [DecidableEq a]
    (A : Mat a) (hA : A.IsHermitian) : matrixLog A = cfc Real.log A := by
  rw [matrixLog,dif_pos hA,hA.cfc_eq]

theorem matrixLog_reindex {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ≃ b) (A : Mat b) (hA : A.IsHermitian) :
    matrixLog (A.submatrix e e) = (matrixLog A).submatrix e e := by
  letI := matrixCStarStructure a
  letI := matrixCStarStructure b
  rw [matrixLog_eq_cfc _ (hA.submatrix _),matrixLog_eq_cfc _ hA]
  exact (StarAlgHomClass.map_cfc (matrixReindexStarEquiv e.symm) Real.log A
    (hφ := (matrixReindexStarEquiv e.symm).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)).symm

theorem matrixLog_block {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : Mat a) (B : Mat b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matrixLog (ClassicalFlag.block A B) = ClassicalFlag.block (matrixLog A) (matrixLog B) := by
  letI := matrixCStarStructure a
  letI := matrixCStarStructure b
  letI := matrixCStarStructure (a ⊕ b)
  rw [matrixLog_eq_cfc _ (ClassicalFlag.block_hermitian A B hA hB),
    matrixLog_eq_cfc _ hA,matrixLog_eq_cfc _ hB]
  have hf : ContinuousOn Real.log (spectrum ℝ A ∪ spectrum ℝ B) := by
    rw [hA.spectrum_real_eq_range_eigenvalues,hB.spectrum_real_eq_range_eigenvalues]
    exact ((Set.finite_range _).union (Set.finite_range _)).continuousOn _
  have hm := (blockPairHom a b).map_cfc Real.log (A,B)
    (hf := by simpa only [Prod.spectrum_eq] using hf)
    (hφ := (blockPairHom a b).toLinearMap.continuous_of_finiteDimensional)
    (ha := show IsSelfAdjoint (A,B) from Prod.ext hA hB)
    (hφa := ClassicalFlag.block_hermitian A B hA hB)
  rw [cfc_map_prod (S := ℂ) Real.log A B (hf := hf) (hab := show IsSelfAdjoint (A,B) from Prod.ext hA hB) (ha := hA) (hb := hB)] at hm
  exact hm.symm

theorem matrixLog_positive_smul {a : Type} [Fintype a] [DecidableEq a]
    (A : Mat a) (hA : A.PosDef) (p : ℝ) (hp : 0 < p) :
    matrixLog ((p : ℂ) • A) = matrixLog A + (Real.log p : ℂ) • 1 := by
  letI := matrixCStarStructure a
  have hpC : (0 : ℂ) < (p : ℂ) := by exact_mod_cast hp
  rw [matrixLog_eq_cfc _ (hA.smul hpC).isHermitian,matrixLog_eq_cfc _ hA.isHermitian]
  change cfc Real.log (p • A) = _
  calc cfc Real.log (p • A) = cfc (fun x => Real.log (p*x)) A :=
         (cfc_comp_const_mul p Real.log A (ha := hA.isHermitian)).symm
       _ = cfc (fun x => Real.log x + Real.log p) A := by
         apply cfc_congr
         intro x hx
         rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
         obtain ⟨i,rfl⟩ := hx
         exact (Real.log_mul hp.ne' (hA.eigenvalues_pos i).ne').trans (add_comm _ _)
       _ = cfc Real.log A + algebraMap ℝ (Mat a) (Real.log p) :=
         cfc_add_const (Real.log p) Real.log A (ha := hA.isHermitian)
       _ = cfc Real.log A + (Real.log p : ℂ) • 1 := by
         rw [Algebra.algebraMap_eq_smul_one]
         rfl

theorem block_posDef {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : Mat a) (B : Mat b)
    (hA : A.PosDef) (hB : B.PosDef) : (ClassicalFlag.block A B).PosDef := by
  apply posDef_iff_dotProduct_mulVec.mpr
  refine ⟨ClassicalFlag.block_hermitian A B hA.isHermitian hB.isHermitian,?_⟩
  intro x hx
  have he : star x ⬝ᵥ (ClassicalFlag.block A B *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
    simp [ClassicalFlag.block,dotProduct,mulVec,Fintype.sum_sum_type]
  rw [he]
  by_cases ha : x ∘ Sum.inl = 0
  · have hb : x ∘ Sum.inr ≠ 0 := by
      intro hb; apply hx; funext i; cases i with
      | inl i => exact congrFun ha i
      | inr i => exact congrFun hb i
    simpa [ha] using (posDef_iff_dotProduct_mulVec.mp hB).2 hb
  · exact add_pos_of_pos_of_nonneg ((posDef_iff_dotProduct_mulVec.mp hA).2 ha)
      ((posSemidef_iff_dotProduct_mulVec.mp hB.posSemidef).2 _)

def flagReference {d : ℕ} (q : Density (Fin d)) (hq : q.matrix.PosDef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : Density (Fin (d+d)) where
  matrix := (ClassicalFlag.block (((1-p : ℝ) : ℂ) • q.matrix)
    ((p : ℂ) • q.matrix)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  positive := by
    apply Matrix.PosSemidef.submatrix
    exact (block_posDef _ _ (hq.smul (show (0 : ℂ) < ((1-p : ℝ) : ℂ) by
      exact_mod_cast sub_pos.mpr hp1)) (hq.smul (show (0 : ℂ) < (p : ℂ) by
      exact_mod_cast hp))).posSemidef
  normalized := by
    rw [submatrix_trace_equiv,ClassicalFlag.block_trace,trace_smul,trace_smul,q.normalized]
    simp

theorem flagReference_faithful {d : ℕ} (q : Density (Fin d)) (hq : q.matrix.PosDef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : (flagReference q hq p hp hp1).matrix.PosDef := by
  apply Matrix.PosDef.submatrix _ finSumFinEquiv.symm.injective
  exact block_posDef _ _ (hq.smul (show (0 : ℂ) < ((1-p : ℝ) : ℂ) by
    exact_mod_cast sub_pos.mpr hp1)) (hq.smul (show (0 : ℂ) < (p : ℂ) by
    exact_mod_cast hp))

theorem flagReference_log {d : ℕ} (q : Density (Fin d)) (hq : q.matrix.PosDef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    matrixLog (flagReference q hq p hp hp1).matrix =
      (ClassicalFlag.block (matrixLog q.matrix + (Real.log (1-p) : ℂ) • 1)
        (matrixLog q.matrix + (Real.log p : ℂ) • 1)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  have ha := (hq.smul (show (0 : ℂ) < ((1-p : ℝ) : ℂ) by
    exact_mod_cast sub_pos.mpr hp1)).isHermitian
  have hb := (hq.smul (show (0 : ℂ) < (p : ℂ) by exact_mod_cast hp)).isHermitian
  change matrixLog ((ClassicalFlag.block _ _).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [matrixLog_reindex _ _ (ClassicalFlag.block_hermitian _ _ ha hb),matrixLog_block _ _ ha hb,
    matrixLog_positive_smul q.matrix hq (1-p) (sub_pos.mpr hp1),matrixLog_positive_smul q.matrix hq p hp]

theorem energy_flagReference_log {d : ℕ} (q : Density (Fin d)) (hq : q.matrix.PosDef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ρ : Density (Fin d)) :
    energy (matrixLog (flagReference q hq p hp hp1).matrix)
      ((ClassicalFlag.block (((1-p : ℝ) : ℂ) • ρ.matrix) ((p : ℂ) • ρ.matrix)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) =
      energy (matrixLog q.matrix) ρ.matrix + (1-p)*Real.log (1-p) + p*Real.log p := by
  rw [flagReference_log,energy_reindex,energy_blocks]
  rw [ClassicalFlag.energy_weight,ClassicalFlag.energy_weight,energy_add,energy_add,
    energy_observable_weight,energy_observable_weight]
  have ho : energy (1 : Mat (Fin d)) ρ.matrix = 1 := by simp [energy,ρ.normalized]
  rw [ho]
  ring

theorem sourceFreeTerm_flag {I : Inventory} {S : Schedule I} (β : ℝ) (e : Extension S)
    (q : Density (Fin e.b)) (hq : q.matrix.PosDef) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    sourceFreeTerm β (ClassicalFlag.extension e e p hp.le hp1.le)
      (flagReference q hq p hp hp1) = sourceFreeTerm β e q := by
  have he (A B : Mat (Fin (e.b+e.b))) :
      (A*B).trace.re = energy B A := congrArg Complex.re (trace_mul_comm _ _)
  unfold sourceFreeTerm faithfulRelativeEntropy
  rw [ClassicalFlag.source_entropy]
  rw [he]
  change (- (ClassicalFlag.binaryEntropy p + (1-p)*entropy e.source.matrix + p*entropy e.source.matrix) -
    energy (matrixLog (flagReference q hq p hp hp1).matrix)
      ((ClassicalFlag.block (((1-p : ℝ) : ℂ) • e.source.matrix) ((p : ℂ) • e.source.matrix)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm))/β = _
  rw [energy_flagReference_log]
  unfold ClassicalFlag.binaryEntropy Real.negMulLog
  have hc : energy (matrixLog q.matrix) e.source.matrix =
      (e.source.matrix*matrixLog q.matrix).trace.re := congrArg Complex.re (trace_mul_comm _ _)
  rw [hc]
  ring

end ScheduleLaw.Blueprint
