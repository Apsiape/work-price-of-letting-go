import InitialRouting
import TerminalRecovery

/-! Rectangular wire kernels and pure-pair insertion, with an arbitrary
untouched reference factor. No realization or operational-map premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

def ketInsert {a z : Type} [DecidableEq z] (v : a → ℂ) : Matrix (a × z) z ℂ :=
  fun i j => v i.1 * if i.2 = j then 1 else 0

theorem ketInsert_sandwich {a z : Type} [Fintype z] [DecidableEq z]
    (v : a → ℂ) (ρ : Mat z) :
    ketInsert (z := z) v * ρ * (ketInsert (z := z) v)ᴴ = pureMatrix v ⊗ₖ ρ := by
  ext i j
  simp [ketInsert,Matrix.mul_apply,Matrix.conjTranspose_apply,pureMatrix,kroneckerMap_apply,
    mul_ite,ite_mul,apply_ite,Finset.sum_ite_irrel]
  ring

theorem cross_sandwich_insert {a b d z : Type} [Fintype a] [Fintype z]
    (C : Matrix a z ℂ) (K : Matrix b a ℂ) (L : Matrix d a ℂ) (ρ : Mat z) :
    K * (C * ρ * Cᴴ) * Lᴴ = (K*C) * ρ * (L*C)ᴴ := by
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem cross_sandwich_eq_of_insert_eq {a b d z : Type} [Fintype a] [Fintype z]
    (C : Matrix a z ℂ) (K K' : Matrix b a ℂ) (L L' : Matrix d a ℂ)
    (hK : K*C = K'*C) (hL : L*C = L'*C) (ρ : Mat z) :
    K * (C*ρ*Cᴴ) * Lᴴ = K' * (C*ρ*Cᴴ) * L'ᴴ := by
  rw [cross_sandwich_insert,cross_sandwich_insert,hK,hL]

theorem kernel_external_interchange {a b z : Type} [Fintype a] [Fintype b] [Fintype z]
    [DecidableEq a] [DecidableEq b] [DecidableEq z] (K : Matrix b a ℂ) (T : Mat z) :
    (K ⊗ₖ (1 : Mat z)) * ((1 : Mat a) ⊗ₖ T) =
      ((1 : Mat b) ⊗ₖ T) * (K ⊗ₖ (1 : Mat z)) := by
  rw [← mul_kronecker_mul,← mul_kronecker_mul]
  simp

theorem kernel_external_density {a b d z : Type} [Fintype a] [Fintype b] [Fintype d]
    [Fintype z] [DecidableEq a] [DecidableEq b] [DecidableEq d] [DecidableEq z]
    (K : Matrix b a ℂ) (L : Matrix d a ℂ) (T : Mat z) (ρ : Mat (a × z)) :
    (K ⊗ₖ (1 : Mat z)) * evolve ((1 : Mat a) ⊗ₖ T) ρ * (L ⊗ₖ (1 : Mat z))ᴴ =
      ((1 : Mat b) ⊗ₖ T) * ((K ⊗ₖ (1 : Mat z)) * ρ * (L ⊗ₖ (1 : Mat z))ᴴ) *
        (((1 : Mat d) ⊗ₖ T)ᴴ) := by
  unfold evolve
  have hL := congrArg Matrix.conjTranspose (kernel_external_interchange L T)
  simp only [Matrix.conjTranspose_mul] at hL
  simp only [← Matrix.mul_assoc]
  rw [kernel_external_interchange]
  simp only [Matrix.mul_assoc]
  rw [hL]

theorem mul_permutation_entry {a b : Type} [Fintype a] [DecidableEq a]
    (K : Matrix b a ℂ) (σ : Equiv.Perm a) (i : b) (j : a) :
    (K * σ.permMatrix ℂ) i j = K i (σ.symm j) := by
  rw [Matrix.mul_apply,← Equiv.sum_comp σ.symm (fun k => K i k * σ.permMatrix ℂ k j)]
  simp [Recorder.permutation_entry]

end ScheduleLaw.History.Wire
