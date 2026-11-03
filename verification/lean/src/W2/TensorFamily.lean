import BlueprintContracts
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.W2

def tensorFamily {ι a : Type} [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a]
    (ρ : ι → Density a) : Mat (ι → a) :=
  fun u v => ∏ i, (ρ i).matrix (u i) (v i)

theorem tensorFamily_positive {ι a : Type} [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a]
    (ρ : ι → Density a) : (tensorFamily ρ).PosSemidef := by
  classical
  have hprod (s : Finset ι) :
      Matrix.PosSemidef (fun u v : ι → a => ∏ i ∈ s, (ρ i).matrix (u i) (v i)) := by
    induction s using Finset.induction_on with
    | empty =>
      have h : (1 : Mat (Fin 1)).PosSemidef := Matrix.PosSemidef.one
      simpa only [Finset.prod_empty,submatrix_apply,one_apply_eq] using
        h.submatrix (fun _ : ι → a => (0 : Fin 1))
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi,Matrix.hadamard_apply] using
        ((ρ i).positive.submatrix (fun u : ι → a => u i)).hadamard ih
  exact hprod Finset.univ

theorem tensorFamily_trace {ι a : Type} [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a]
    (ρ : ι → Density a) : (tensorFamily ρ).trace=1 := by
  classical
  change (∑ u : ι → a, ∏ i, (ρ i).matrix (u i) (u i))=1
  rw [← Fintype.prod_sum (fun (i : ι) (j : a) => (ρ i).matrix j j)]
  have h (i : ι) : (∑ j, (ρ i).matrix j j)=1 := (ρ i).normalized
  simp only [h,Finset.prod_const_one]

def tensorFamilyDensity {ι a : Type} [Fintype ι] [DecidableEq ι] [Fintype a] [DecidableEq a]
    (ρ : ι → Density a) : Density (ι → a) :=
  ⟨tensorFamily ρ,tensorFamily_positive ρ,tensorFamily_trace ρ⟩

end ScheduleLaw.Blueprint.W2
