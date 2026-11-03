import FiniteFlatModel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FlatOutput
open FiniteFlat

theorem run_one {d : ℕ} {β x : ℝ} (C : SupportConverter β (zeroHamiltonian d) x) (ρ : Mat (Fin d)) :
    C.run 1 (ρ ⊗ₖ (1 : Mat (Fin 1))) =
      evolve C.U (ρ ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=0 then 1 else 0) ⊗ₖ gibbs β C.HR)) ⊗ₖ
        (1 : Mat (Fin 1)) := by
  ext ⟨i,z⟩ ⟨j,w⟩
  fin_cases z
  fin_cases w
  simp [SupportConverter.run,evolve,Matrix.mul_apply,Fintype.sum_prod_type,
    converterFrame,Matrix.kroneckerMap_apply]

theorem trace_one {a : Type} [Fintype a] (A : Mat a) :
    partialRight (A ⊗ₖ (1 : Mat (Fin 1)))=A := by
  ext i j
  simp [partialRight,Matrix.kroneckerMap_apply]

theorem flatOutput_eq {d : ℕ} {β x : ℝ} (C : SupportConverter β (zeroHamiltonian d) x) :
    flatOutput C = partialRight (
      ((1 : Mat (Fin d)) ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ (1 : Mat (Fin C.r)))) *
      evolve C.U ((((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ
        (pureMatrix (fun j : Fin 2 => if j=0 then 1 else 0) ⊗ₖ gibbs β C.HR))) := by
  unfold flatOutput
  rw [run_one,←mul_kronecker_mul,one_mul,trace_one]

theorem initial_diagonal (d r : ℕ) (w : Fin r → ℂ) :
    ((((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ
      (pureMatrix (fun j : Fin 2 => if j=0 then 1 else 0) ⊗ₖ diagonal w)) =
      diagonal (fun o : Fin d × (Fin 2 × Fin r) =>
        if o.2.1=0 then (d : ℂ)⁻¹*w o.2.2 else 0) := by
  ext ⟨i,b,u⟩ ⟨j,c,v⟩
  fin_cases b <;> fin_cases c <;> by_cases hij : i=j <;> by_cases huv : u=v <;>
    simp_all [Matrix.kroneckerMap_apply,Matrix.of_apply,Matrix.diagonal,pureMatrix]

theorem mask_diagonal (d r : ℕ) :
    ((1 : Mat (Fin d)) ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ (1 : Mat (Fin r)))) =
      diagonal (fun o : Fin d × (Fin 2 × Fin r) => if o.2.1=1 then 1 else 0) := by
  ext ⟨i,b,u⟩ ⟨j,c,v⟩
  fin_cases b <;> fin_cases c <;> by_cases hij : i=j <;> by_cases huv : u=v <;>
    simp_all [Matrix.kroneckerMap_apply,Matrix.of_apply,Matrix.diagonal,pureMatrix]

theorem permutation_diagonal {a : Type} [Fintype a] [DecidableEq a] (σ : Equiv.Perm a) (p : a → ℂ) :
    evolve (σ.permMatrix ℂ) (diagonal p) = diagonal (fun i => p (σ i)) := by
  rw [Recorder.permutation_evolve]
  ext i j
  by_cases h : i=j
  · subst j; simp
  · simp [Matrix.diagonal,h,σ.injective.ne h]

theorem trace_diagonal {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (p : a × b → ℂ) : partialRight (diagonal p) = diagonal (fun i => ∑ j,p (i,j)) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [partialRight]
  · simp [partialRight,Matrix.diagonal,h]

theorem output_permutation {d : ℕ} {β x : ℝ} (C : SupportConverter β (zeroHamiltonian d) x)
    (σ : Equiv.Perm (Fin d × (Fin 2 × Fin C.r))) (w : Fin C.r → ℂ)
    (hU : C.U=σ.permMatrix ℂ) (hγ : gibbs β C.HR=diagonal w) :
    flatOutput C = diagonal (fun i => ∑ r : Fin C.r,
      if (σ (i,1,r)).2.1=0 then (d : ℂ)⁻¹*w (σ (i,1,r)).2.2 else 0) := by
  rw [flatOutput_eq,hU,hγ,initial_diagonal,permutation_diagonal,mask_diagonal,
    diagonal_mul_diagonal,trace_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  simp [Fintype.sum_prod_type,Fin.sum_univ_two]
end ScheduleLaw.Blueprint.FlatOutput
