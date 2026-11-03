import FactoryPlacement
import FactoryPreparedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryFlagEffects
open History

variable {a u v : Type} [Fintype a] [Fintype u] [Fintype v]
  [DecidableEq a] [DecidableEq u] [DecidableEq v]

def effect (flag : a → Fin 2) : Mat a := diagonal (fun j => if flag j=1 then 1 else 0)
def success (flag : a → Fin 2) (ρ : Mat a) : ℝ := energy (effect flag) ρ

theorem success_sum (flag : a → Fin 2) (ρ : Mat a) :
    success flag ρ=∑ j,if flag j=1 then (ρ j j).re else 0 := by
  simp only [success,effect,energy,diagonal_mul,Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

def opposite (flag : a → Fin 2) (j : a) : Fin 2 := if flag j=1 then 0 else 1

theorem opposite_success (flag : a → Fin 2) (ρ : Mat a) :
    success (opposite flag) ρ=ρ.trace.re-success flag ρ := by
  rw [success_sum,success_sum]
  simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hf : flag j=1 <;> simp [opposite,hf]

theorem success_reindex {b : Type} [Fintype b] [DecidableEq b]
    (e : a ≃ b) (flag : b → Fin 2) (ρ : Mat b) :
    success (fun j => flag (e j)) (ρ.submatrix e e)=success flag ρ := by
  have he : effect (fun j => flag (e j))=(effect flag).submatrix e e := by
    rw [effect,effect,submatrix_diagonal_equiv]
    rfl
  unfold success
  rw [he,energy_reindex]

theorem permutation_success (π : Equiv.Perm a) (flag : a → Fin 2)
    (hf : ∀ j,flag (π j)=flag j) (ρ : Mat a) :
    success flag (evolve (π.permMatrix ℂ) ρ)=success flag ρ := by
  rw [Recorder.permutation_evolve]
  have he : (fun j => flag (π j))=flag := funext hf
  simpa only [he] using (success_reindex π flag ρ)

theorem local_success (E : a ≃ u × v) (flag : u → Fin 2) (ρ : Mat a) :
    success (fun j => flag (E j).1) ρ =
      success flag (partialRight (ρ.submatrix E.symm E.symm)) := by
  have he : effect (fun j => flag (E j).1)=((effect flag) ⊗ₖ (1 : Mat v)).submatrix E E := by
    ext i j
    simp only [effect,submatrix_apply,kroneckerMap_apply,Matrix.diagonal_apply,one_apply]
    have hi : i=j ↔ (E i).1=(E j).1 ∧ (E i).2=(E j).2 := by
      rw [← E.injective.eq_iff]
      exact Prod.ext_iff
    split_ifs <;> simp_all
  have hρ : (ρ.submatrix E.symm E.symm).submatrix E E=ρ := by
    ext i j
    simp only [submatrix_apply,Equiv.symm_apply_apply]
  unfold success
  calc
    _ = energy (((effect flag) ⊗ₖ (1 : Mat v)).submatrix E E)
        ((ρ.submatrix E.symm E.symm).submatrix E E) := by rw [hρ,he]
    _ = energy ((effect flag) ⊗ₖ (1 : Mat v)) (ρ.submatrix E.symm E.symm) :=
      energy_reindex E _ _
    _ = _ := energy_kron_one _ _

/-- Every flag that is a coordinate of the complete retained rest is conserved
by a placed unitary, including arbitrary coherent and correlated inputs. -/
theorem disjoint_success (E : a ≃ u × v) (flag : a → Fin 2) (outside : v → Fin 2)
    (hf : ∀ i,flag i=outside (E i).2) (U : Mat u) (hU : IsUnitary U) (ρ : Mat a) :
    success flag (evolve (FactoryPlacement.place E U) ρ)=success flag ρ := by
  have he : effect flag=((1 : Mat u) ⊗ₖ effect outside).submatrix E E := by
    ext i j
    simp only [effect,submatrix_apply,kroneckerMap_apply,Matrix.diagonal_apply,one_apply,hf]
    have hi : i=j ↔ (E i).1=(E j).1 ∧ (E i).2=(E j).2 := by
      rw [← E.injective.eq_iff]
      exact Prod.ext_iff
    split_ifs <;> simp_all
  have hc : Conserves (FactoryPlacement.place E U) (effect flag) := by
    have h := FactoryPlacement.conserves E U (0 : Mat u) (effect outside) hU
      (by simp [Conserves])
    simpa only [zero_kronecker,zero_add,← he] using h
  unfold success
  rw [energy_pullback,hc]

/-- The physical success projection of a converter is exactly its work flag. -/
theorem converter_effect {b t : Type} [Fintype b] [Fintype t]
    [DecidableEq b] [DecidableEq t] :
    effect (fun z : b × (Fin 2 × t) => z.2.1)=
      (1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat t)) := by
  rw [SupportRun.level_diagonal]
  change diagonal _=diagonal (fun _ : b => (1 : ℂ)) ⊗ₖ
    (diagonal (fun w : Fin 2 => if w=1 then 1 else 0) ⊗ₖ diagonal (fun _ : t => (1 : ℂ)))
  rw [diagonal_kronecker_diagonal,diagonal_kronecker_diagonal]
  simp only [one_mul,mul_one]

end ScheduleLaw.Blueprint.FactoryFlagEffects
