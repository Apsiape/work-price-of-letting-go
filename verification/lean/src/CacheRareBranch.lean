import CacheMixture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheRareBranch
open History CacheFlaggedCircuit CacheBatchSplit

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def stock (F : Formation β τ q (n+1)) : Mat ((Fin 2 × Fin 2) × (Fin d × CacheFactoryBody.Rest F)) :=
  level ((1 : Fin 2),(0 : Fin 2)) ⊗ₖ (τ.matrix ⊗ₖ CacheFactoryBody.helper F)

def idealSector (F : Formation β τ q (n+1)) (j : Fin (n+1)) : Mat (Physical F) :=
  ((level (CacheClockAdvance.step n j) ⊗ₖ
    (cacheSector τ q n (CacheClockAdvance.step n j)).matrix) ⊗ₖ stock F).submatrix (frame F) (frame F)

def ideal (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  ((n+1 : ℝ)⁻¹) • ∑ j : Fin (n+1), idealSector F j

theorem nonboundary_ideal (F : Formation β τ q (n+1)) (j : Fin (n+1)) (hj : j≠0) :
    evolve (circuit F) (inputSector F j)=idealSector F j := by
  rw [CacheFlaggedCircuit.nonboundary F j hj]
  ext i i'
  obtain ⟨⟨⟨k,u⟩,⟨w,v⟩,b,r⟩,rfl⟩ := (frame F).symm.surjective i
  obtain ⟨⟨⟨k',u'⟩,⟨w',v'⟩,b',r'⟩,rfl⟩ := (frame F).symm.surjective i'
  have ht := congrFun (congrFun (emitted τ q n j hj) (b,u)) (b',u')
  simp only [submatrix_apply,kroneckerMap_apply] at ht
  have hf := congrArg (fun M : Mat (Fin (n+1) × (Fin 2 × Fin 2)) =>
    M (k,w,v) (k',w',v')) (level_prod (CacheClockAdvance.step n j) ((1 : Fin 2),(0 : Fin 2)))
  simp only [kroneckerMap_apply] at hf
  simp only [idealSector,submatrix_apply,Equiv.apply_symm_apply]
  simp only [frame,Equiv.coe_fn_symm_mk,kroneckerMap_apply,stock,CacheClockAdvance.target,if_neg hj]
  rw [hf,ht]
  ring

theorem ideal_product (F : Formation β τ q (n+1)) :
    (ideal F).submatrix (frame F).symm (frame F).symm =
      cacheState τ q (n+1) ⊗ₖ stock F := by
  rw [ideal,CacheMixture.cache_decomposition]
  ext i j
  simp only [submatrix_apply,smul_apply,Matrix.sum_apply,idealSector,
    Equiv.apply_symm_apply,kroneckerMap_apply,Complex.real_smul]
  rw [← Finset.sum_mul]
  have hs := Equiv.sum_comp (CacheClockAdvance.step n)
    (fun k => level k i.1.1 j.1.1 * (cacheSector τ q n k).matrix i.1.2 j.1.2)
  rw [hs]
  ring

theorem difference (F : Formation β τ q (n+1)) :
    CacheMixture.output F-ideal F = ((n+1 : ℝ)⁻¹) •
      (evolve (circuit F) (inputSector F 0)-idealSector F 0) := by
  rw [CacheMixture.run_mixture,ideal,← smul_sub,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_eq_single (0 : Fin (n+1))
  · intro j hj hj0
    rw [nonboundary_ideal F j hj0,sub_self]
  · simp

theorem ideal_sector_density (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    (idealSector F j).PosSemidef ∧ (idealSector F j).trace=1 := by
  obtain ⟨hp,ht⟩ := CacheMixture.helper_density F
  constructor
  · exact ((pureMatrix_positive _).kronecker (cacheSector τ q n _).positive).kronecker
      ((pureMatrix_positive _).kronecker (τ.positive.kronecker hp)) |>.submatrix _
  · rw [idealSector,submatrix_trace_equiv]
    simp only [stock,trace_kronecker,(cacheSector τ q n _).normalized,
      τ.normalized,ht,mul_one,one_mul,level]
    rw [pureMatrix_trace,pureMatrix_trace]
    simp

theorem actual_sector_density (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    (evolve (circuit F) (inputSector F j)).PosSemidef ∧
      (evolve (circuit F) (inputSector F j)).trace=1 := by
  obtain ⟨hp,ht⟩ := CacheMixture.input_sector_density F j
  exact ⟨hp.mul_mul_conjTranspose_same _,(evolve_trace _ _ (circuit_unitary F)).trans ht⟩

theorem distance (F : Formation β τ q (n+1)) :
    traceDistance (CacheMixture.output F) (ideal F) ≤ (n+1 : ℝ)⁻¹ := by
  let A : Density (Physical F) := ⟨_,(actual_sector_density F 0).1,(actual_sector_density F 0).2⟩
  let B : Density (Physical F) := ⟨_,(ideal_sector_density F 0).1,(ideal_sector_density F 0).2⟩
  have he : ((n+1 : ℝ)⁻¹) • (A.matrix-B.matrix) =
      (((n+1 : ℝ)⁻¹ : ℝ) : ℂ) • (A.matrix-B.matrix) := by
    ext i j
    simp only [smul_apply,Complex.real_smul,smul_eq_mul]
  have hd := ClassicalFlag.density_distance_le_one A B
  unfold traceDistance at *
  rw [difference,ClassicalFlag.traceNorm_eq_library]
  change Matrix.traceNorm (((n+1 : ℝ)⁻¹) • (A.matrix-B.matrix))/2 ≤ _
  rw [he,Matrix.traceNorm_smul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(n+1 : ℝ)⁻¹)]
  rw [ClassicalFlag.traceNorm_eq_library] at hd
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0≤(n+1 : ℝ)⁻¹)]

end ScheduleLaw.Blueprint.CacheRareBranch
