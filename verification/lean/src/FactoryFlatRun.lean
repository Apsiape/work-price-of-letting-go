import FactoryOutput
import SupportRunGeneral
import FactoryFormation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFlatRun
open History

/-- The actual converter on an independent reference is the local run tensored
with that reference. This equality includes every failure column. -/
theorem run_product {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (z : ℕ) (ρ : Mat (Fin d)) (σ : Mat (Fin z)) :
    C.run z (ρ ⊗ₖ σ) =
      evolve C.U (ρ ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)) ⊗ₖ σ := by
  have hi : ((ρ ⊗ₖ σ) ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)).submatrix
      (converterFrame d C.r z).symm (converterFrame d C.r z).symm =
      (ρ ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)) ⊗ₖ σ := by
    ext ⟨⟨i,⟨w,b⟩⟩,k⟩ ⟨⟨j,⟨v,c⟩⟩,h⟩
    simp only [submatrix_apply,converterFrame,Equiv.coe_fn_symm_mk,kroneckerMap_apply]
    ring
  unfold SupportConverter.run
  change evolve (C.U ⊗ₖ (1 : Mat (Fin z)))
    (((ρ ⊗ₖ σ) ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)).submatrix
      (converterFrame d C.r z).symm (converterFrame d C.r z).symm)=_
  rw [hi]
  simp only [evolve,conjTranspose_kronecker,conjTranspose_one,
    ← mul_kronecker_mul,one_mul,mul_one]

def state {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (ρ : Density (Fin d)) :
    Density (Fin d × (Fin 2 × Fin C.r)) := by
  letI : Nonempty (Fin C.r) := ⟨⟨0,C.r_pos⟩⟩
  let A := ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)
  have hA : A.PosSemidef := ρ.positive.kronecker
    ((pureMatrix_positive _).kronecker (gibbs_positive β C.HR))
  have ht : A.trace=1 := by
    rw [trace_kronecker,trace_kronecker,ρ.normalized,SupportRun.level_trace,gibbs_trace]
    norm_num
  exact ⟨evolve C.U A,(evolve_density C.U A C.unitary hA ht).1,
    (evolve_density C.U A C.unitary hA ht).2⟩

theorem success_marginal {a c : Type} [Fintype a] [Fintype c]
    [DecidableEq a] [DecidableEq c] (ρ : Mat (a × (Fin 2 × c))) :
    partialRight (((1 : Mat a) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c)))*ρ) =
      FactoryOutput.branch ρ 1 := by
  have he : ((1 : Mat a) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c))) =
      diagonal (fun z : a × (Fin 2 × c) => if z.2.1=1 then 1 else 0) := by
    rw [SupportRun.level_diagonal]
    change diagonal (fun _ : a => (1 : ℂ)) ⊗ₖ
      ((diagonal (fun w : Fin 2 => if w=1 then 1 else 0)) ⊗ₖ
        diagonal (fun _ : c => (1 : ℂ)))=_
    rw [diagonal_kronecker_diagonal,diagonal_kronecker_diagonal]
    simp only [mul_one,one_mul]
  rw [he]
  ext i j
  simp only [partialRight,FactoryOutput.branch,submatrix_apply,diagonal_mul,
    Fintype.sum_prod_type,Fin.sum_univ_two]
  simp

/-- Bridge the original exact-flat theorem's reference-one expression to the
literal unconditional local converter state used in the physical circuit. -/
theorem flatOutput_eq_branch {d : ℕ} {β x : ℝ}
    (C : SupportConverter β (FiniteFlat.zeroHamiltonian d) x) (hd : 0<d) :
    FiniteFlat.flatOutput C =
      FactoryOutput.branch (state C (FactoryFormation.flat d hd)).matrix 1 := by
  rw [FiniteFlat.flatOutput,run_product]
  rw [← mul_kronecker_mul,one_mul,partialRight_kron]
  simp only [trace_one,Fintype.card_fin,Nat.cast_one,one_smul]
  apply success_marginal

end ScheduleLaw.Blueprint.FactoryFlatRun
