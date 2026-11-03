import CacheBatchSplit
import CacheState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheMixture
open History CacheFlaggedCircuit CacheBatchSplit

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def input (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  ((n+1 : ℝ)⁻¹) • ∑ j : Fin (n+1), inputSector F j

def output (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  evolve (circuit F) (input F)

theorem cache_decomposition (τ q : Density (Fin d)) (n : ℕ) :
    cacheState τ q (n+1) = ((n+1 : ℝ)⁻¹) •
      ∑ j : Fin (n+1), level j ⊗ₖ (cacheSector τ q n j).matrix := by
  have hlev (j k l : Fin (n+1)) : level j k l=if k=j ∧ l=j then 1 else 0 := by
    by_cases hk : k=j <;> by_cases hl : l=j <;> simp [level,pureMatrix,hk,hl]
  have hp (j : Fin (n+1)) (u v : Fin n → Fin d) :
      (∏ l, (if l.val<j.val then τ.matrix else q.matrix) (u l) (v l))=
        (cacheSector τ q n j).matrix u v := by
    apply Finset.prod_congr rfl
    intro l hl
    by_cases hh : l.val<j.val <;> simp [hh]
  ext ⟨k,u⟩ ⟨l,v⟩
  by_cases hkl : k=l
  · subst l
    simp only [cacheState,if_true,smul_apply,Matrix.sum_apply,kroneckerMap_apply,hlev,
      and_self,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true,hp]
    simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_one,
      Nat.cast_add,Nat.cast_one,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    exact congrArg (fun z : ℂ => (n+1 : ℂ)⁻¹*z) (hp k u v)
  · have hbad (j : Fin (n+1)) : ¬(k=j ∧ l=j) := fun h => hkl (h.1.trans h.2.symm)
    simp only [cacheState,if_neg hkl,smul_apply,Matrix.sum_apply,kroneckerMap_apply,hlev,
      if_neg (hbad _),zero_mul,Finset.sum_const_zero,smul_zero]

theorem input_product (F : Formation β τ q (n+1)) :
    (input F).submatrix (frame F).symm (frame F).symm =
      cacheState τ q (n+1) ⊗ₖ
        (level ((0 : Fin 2),(0 : Fin 2)) ⊗ₖ (q.matrix ⊗ₖ CacheFactoryBody.helper F)) := by
  rw [input,cache_decomposition]
  ext i j
  simp only [submatrix_apply,smul_apply,Matrix.sum_apply,kroneckerMap_apply,
    Complex.real_smul,Finset.sum_mul]
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have h := congrArg (fun M => M i j) (input_sector F k)
  simpa only [submatrix_apply,kroneckerMap_apply,mul_assoc] using h

theorem helper_density (F : Formation β τ q (n+1)) :
    (CacheFactoryBody.helper F).PosSemidef ∧ (CacheFactoryBody.helper F).trace=1 := by
  letI : Nonempty (Fin F.aux) := ⟨⟨0,F.aux_pos⟩⟩
  constructor
  · exact F.hardware.controller.positive.kronecker
      ((pureMatrix_positive _).kronecker (gibbs_positive β F.auxiliaryHamiltonian))
  · simp only [CacheFactoryBody.helper,trace_kronecker,F.hardware.controller.normalized,
      gibbs_trace,mul_one,one_mul]
    rw [pureMatrix_trace]
    simp

theorem input_sector_density (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    (inputSector F j).PosSemidef ∧ (inputSector F j).trace=1 := by
  obtain ⟨hp,ht⟩ := helper_density F
  constructor
  · exact (pureMatrix_positive _).kronecker
      ((W2.tensorFamily_positive _).kronecker hp)
  · simp only [inputSector,trace_kronecker,W2.tensorFamily_trace,ht,mul_one,one_mul,level]
    rw [pureMatrix_trace]
    simp

theorem input_density (F : Formation β τ q (n+1)) :
    (input F).PosSemidef ∧ (input F).trace=1 := by
  constructor
  · exact (Matrix.posSemidef_sum Finset.univ (fun j _ => (input_sector_density F j).1)).smul
      (by positivity : 0≤(n+1 : ℝ)⁻¹)
  · simp only [input,trace_smul,trace_sum,(input_sector_density F _).2,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,
      Complex.ofReal_add,Complex.ofReal_one,Nat.cast_add,Nat.cast_one]
    exact inv_mul_cancel₀ (by positivity : (n+1 : ℂ)≠0)

theorem run_mixture (F : Formation β τ q (n+1)) :
    output F = ((n+1 : ℝ)⁻¹) • ∑ j : Fin (n+1), evolve (circuit F) (inputSector F j) := by
  simp only [output,input,evolve,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul]

end ScheduleLaw.Blueprint.CacheMixture
