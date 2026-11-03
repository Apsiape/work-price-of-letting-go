import FiniteSwap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FlatMatrix
open History

def diagonalHom (a : Type) [Fintype a] [DecidableEq a] : (a → ℂ) →⋆ₐ[ℂ] Mat a :=
  { Matrix.diagonalAlgHom (n:=a) (α:=ℂ) ℂ with
    map_star' := fun f => by simp [star_eq_conjTranspose,diagonal_conjTranspose] }

def diagonalHamiltonian (a : Type) [Fintype a] [DecidableEq a] (E : a → ℝ) : Hamiltonian a :=
  ⟨diagonal (fun i => (E i : ℂ)),by
    ext i j
    by_cases h : i=j
    · subst j; simp
    · simp [Matrix.diagonal,h,Ne.symm h]⟩

theorem diagonal_cfc (a : Type) [Fintype a] [DecidableEq a]
    (E : a → ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (diagonalHamiltonian a E).hermitian.cfc f = diagonal (fun i => (f (E i) : ℂ)) := by
  letI := matrixCStarStructure a
  rw [← Matrix.IsHermitian.cfc_eq]
  have hm := (diagonalHom a).map_cfc f (fun i => (E i : ℂ))
    (hf := hf.continuousOn)
    (hφ := (diagonalHom a).toLinearMap.continuous_of_finiteDimensional)
    (ha := by ext i; simp)
    (hφa := (diagonalHamiltonian a E).hermitian)
  change cfc f (diagonalHom a (fun i => (E i : ℂ))) = _
  rw [← hm]
  apply congrArg Matrix.diagonal
  rw [cfc_map_pi (S:=ℂ) f _ (hf:=hf.continuousOn) (ha:=by ext i; simp) (ha':=by intro i; simp [IsSelfAdjoint])]
  funext i
  exact cfc_algebraMap (A:=ℂ) (E i) f

theorem diagonal_partition (a : Type) [Fintype a] [DecidableEq a]
    (E : a → ℝ) (β : ℝ) :
    partition β (diagonalHamiltonian a E) = ∑ i,Real.exp (-β*E i) := by
  have ht := congrArg Matrix.trace (diagonal_cfc a E (fun x => Real.exp (-β*x)) (by fun_prop))
  unfold Matrix.IsHermitian.cfc at ht
  rw [trace_unitary_conjugation] at ht
  simp only [trace_diagonal,Function.comp_apply] at ht
  change (∑ i,(Real.exp (-β*(diagonalHamiltonian a E).hermitian.eigenvalues i) : ℂ)) =
    (∑ i,(Real.exp (-β*E i) : ℂ)) at ht
  rw [←Complex.ofReal_sum,←Complex.ofReal_sum] at ht
  exact Complex.ofReal_injective ht

theorem diagonal_gibbs (a : Type) [Fintype a] [DecidableEq a]
    (E : a → ℝ) (β : ℝ) :
    gibbs β (diagonalHamiltonian a E) =
      diagonal (fun i => ((Real.exp (-β*E i)/(∑ j,Real.exp (-β*E j)) : ℝ) : ℂ)) := by
  change (diagonalHamiltonian a E).hermitian.cfc
    (fun x => Real.exp (-β*x)/partition β (diagonalHamiltonian a E)) = _
  rw [diagonal_partition]
  exact diagonal_cfc a E _ (by fun_prop)
end ScheduleLaw.Blueprint.FlatMatrix



