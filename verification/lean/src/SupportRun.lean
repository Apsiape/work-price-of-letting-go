import SupportSwapEffect
import ThermalContactEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportRun
open History

def level (j : Fin 2) : Mat (Fin 2) :=
  pureMatrix (fun k => if k=j then 1 else 0)

theorem level_diagonal (j : Fin 2) : level j = diagonal (fun k => if k=j then 1 else 0) := by
  ext i k
  by_cases hi : i=j <;> by_cases hk : k=j <;>
    simp_all [level,pureMatrix,Matrix.diagonal,eq_comm]

theorem level_idem (j : Fin 2) : level j*level j=level j := by
  rw [level_diagonal,diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> norm_num

theorem level_trace (j : Fin 2) : (level j).trace=1 := by
  rw [level_diagonal,trace_diagonal]
  simp

theorem initialized_expectation {d r z : ℕ} (P : Mat (Fin d)) (G γ : Mat (Fin r))
    (ρ : Density (Fin d × Fin z)) (hρ : (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix) :
    energy ((P ⊗ₖ (level 0 ⊗ₖ G)) ⊗ₖ (1 : Mat (Fin z)))
      ((ρ.matrix ⊗ₖ (level 0 ⊗ₖ γ)).submatrix
        (converterFrame d r z).symm (converterFrame d r z).symm) = energy G γ := by
  have he : ((P ⊗ₖ (level 0 ⊗ₖ G)) ⊗ₖ (1 : Mat (Fin z))) =
      (((P ⊗ₖ (1 : Mat (Fin z))) ⊗ₖ (level 0 ⊗ₖ G)).submatrix
        (converterFrame d r z).symm (converterFrame d r z).symm) := by
    ext ⟨⟨i,⟨w,b⟩⟩,k⟩ ⟨⟨j,⟨v,c⟩⟩,h⟩
    simp only [submatrix_apply,converterFrame,Equiv.coe_fn_symm_mk,
      kroneckerMap_apply]
    ring
  rw [he,energy_reindex]
  unfold energy
  rw [← mul_kronecker_mul,hρ,trace_kronecker,ρ.normalized,one_mul,
    ← mul_kronecker_mul,trace_kronecker,level_idem,level_trace,one_mul]

theorem probability {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (P Q : Mat (Fin d)) (G : Mat (Fin C.r))
    (hgap : (C.Uᴴ*(Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U -
      P ⊗ₖ (level 0 ⊗ₖ G)).PosSemidef)
    (z : ℕ) (ρ : Density (Fin d × Fin z))
    (hsupport : (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix) :
    energy G (gibbs β C.HR) ≤
      energy ((Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  letI : Nonempty (Fin C.r) := ⟨⟨0,C.r_pos⟩⟩
  let N := ((ρ.matrix ⊗ₖ (level 0 ⊗ₖ gibbs β C.HR)).submatrix
    (converterFrame d C.r z).symm (converterFrame d C.r z).symm)
  have hN : N.PosSemidef := (ρ.positive.kronecker
    ((pureMatrix_positive _).kronecker (gibbs_positive β C.HR))).submatrix _
  have hfull : (((C.Uᴴ*(Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U) ⊗ₖ
      (1 : Mat (Fin z))) - (P ⊗ₖ (level 0 ⊗ₖ G)) ⊗ₖ (1 : Mat (Fin z))).PosSemidef := by
    convert hgap.kronecker (Matrix.PosSemidef.one : (1 : Mat (Fin z)).PosSemidef) using 1
    ext ⟨i,k⟩ ⟨j,l⟩
    simp only [kroneckerMap_apply,Matrix.sub_apply]
    ring
  have hm := SupportEffect.energy_mono _ _ N hfull hN
  rw [initialized_expectation P G (gibbs β C.HR) ρ hsupport] at hm
  unfold SupportConverter.run
  rw [energy_pullback]
  simpa only [conjTranspose_kronecker,conjTranspose_one,← mul_kronecker_mul,
    one_mul,mul_one] using hm

end ScheduleLaw.Blueprint.SupportRun
