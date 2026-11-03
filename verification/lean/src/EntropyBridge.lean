/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE-APACHE-2.0.txt.

Modified for this relay: selected characteristic-polynomial entropy proofs from
LionSR/QICLean, revision 820533fa68cf37999aa9e56d3e44b9423c4d0325,
TNLean/Analysis/Entropy.lean, were adapted to ScheduleLaw.entropy and Mathlib
v4.30.0. No TNLean imports, axioms or unproved declarations are used.
The final pure-complement matrix calculation was added for this relay.
-/
import Foundations

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace ScheduleLaw

/-- Adapted from vonNeumannEntropy_eq_charpoly_roots at the pin above. -/
theorem entropy_eq_charpoly_roots {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Mat n) (hρ : ρ.IsHermitian) :
    entropy ρ = (ρ.charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  rw [entropy, dif_pos hρ]
  have hmap : (Finset.univ : Finset n).val.map hρ.eigenvalues =
      ρ.charpoly.roots.map Complex.re := by
    rw [hρ.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => by simp
  calc ∑ i, Real.negMulLog (hρ.eigenvalues i)
      = (((Finset.univ : Finset n).val.map hρ.eigenvalues).map Real.negMulLog).sum := by
        rw [Multiset.map_map]; rfl
    _ = ((ρ.charpoly.roots.map Complex.re).map Real.negMulLog).sum := by rw [hmap]
    _ = (ρ.charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum := by
        rw [Multiset.map_map]; rfl

/-- Adapted from charpoly_roots_negMulLog_re_mul_comm at the pin above. -/
theorem charpoly_entropy_mul_comm {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    ((A * B).charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum =
      ((B * A).charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  set f : ℂ → ℝ := fun z => Real.negMulLog z.re with hf
  have hroots : (Polynomial.X ^ Fintype.card n * (A * B).charpoly).roots =
      (Polynomial.X ^ Fintype.card m * (B * A).charpoly).roots := by
    rw [Matrix.charpoly_mul_comm']
  rw [Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
      Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
      Polynomial.roots_pow, Polynomial.roots_pow, Polynomial.roots_X] at hroots
  have hf0 : f 0 = 0 := by simp [hf]
  have key := congrArg (fun s => (Multiset.map f s).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, hf0, smul_zero, zero_add] at key
  exact key

/-- Adapted from vonNeumannEntropy_mul_comm at the pin above. -/
theorem entropy_mul_comm {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hAB : (A * B).IsHermitian) (hBA : (B * A).IsHermitian) :
    entropy (A * B) = entropy (B * A) := by
  rw [entropy_eq_charpoly_roots _ hAB, entropy_eq_charpoly_roots _ hBA]
  exact charpoly_entropy_mul_comm A B

/-- Adapted from vonNeumannEntropy_transpose at the pin above. -/
theorem entropy_transpose {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Mat n) (hρ : ρ.IsHermitian) : entropy ρᵀ = entropy ρ := by
  rw [entropy_eq_charpoly_roots _ hρ.transpose, entropy_eq_charpoly_roots _ hρ,
    Matrix.charpoly_transpose]

/-- Complementary reductions of a finite pure vector have equal entropy. No
normalization is required; extra zero eigenvalues contribute zero entropy. -/
theorem pure_complement_entropy {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ψ : a × b → ℂ) :
    entropy (partialRight (pureMatrix ψ)) = entropy (partialLeft (pureMatrix ψ)) := by
  let A : Matrix a b ℂ := fun i j => ψ (i, j)
  have hr : partialRight (pureMatrix ψ) = A * Aᴴ := by
    ext i j
    simp [partialRight, pureMatrix, Matrix.mul_apply, A]
  have hl : partialLeft (pureMatrix ψ) = (Aᴴ * A)ᵀ := by
    ext i j
    simp [partialLeft, pureMatrix, Matrix.mul_apply, A, mul_comm]
  rw [hr, hl, entropy_transpose _ (posSemidef_conjTranspose_mul_self A).isHermitian]
  exact entropy_mul_comm A Aᴴ (posSemidef_self_mul_conjTranspose A).isHermitian
    (posSemidef_conjTranspose_mul_self A).isHermitian

end ScheduleLaw
