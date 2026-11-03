import BlueprintContracts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FiniteResidue

/-- Full square tensor power, with all coherent matrix entries. -/
def tensorMatrix {a : Type} [Fintype a] (A : Mat a) (m : ℕ) : Mat (Fin m → a) :=
  fun u v => ∏ i, A (u i) (v i)

theorem tensorMatrix_mul {a : Type} [Fintype a] (A B : Mat a) (m : ℕ) :
    tensorMatrix (A*B) m = tensorMatrix A m * tensorMatrix B m := by
  classical
  ext u v
  change (∏ i, ∑ j, A (u i) j * B j (v i)) =
    ∑ w : Fin m → a, (∏ i, A (u i) (w i)) * (∏ i, B (w i) (v i))
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.prod_mul_distrib

theorem tensorMatrix_star {a : Type} [Fintype a] (A : Mat a) (m : ℕ) :
    tensorMatrix Aᴴ m = (tensorMatrix A m)ᴴ := by
  ext u v
  simp [tensorMatrix,Matrix.conjTranspose_apply]

theorem tensorMatrix_one {a : Type} [Fintype a] [DecidableEq a] (m : ℕ) :
    tensorMatrix (1 : Mat a) m = 1 := by
  classical
  ext u v
  by_cases huv : u=v
  · subst v
    simp [tensorMatrix]
  · obtain ⟨i,hi⟩ : ∃ i, u i ≠ v i := by
      by_contra h
      push Not at h
      exact huv (funext h)
    change (∏ j, (1 : Mat a) (u j) (v j)) = (1 : Mat (Fin m → a)) u v
    rw [Matrix.one_apply_ne huv]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem tensorMatrix_diagonal {a : Type} [Fintype a] [DecidableEq a]
    (p : a → ℂ) (m : ℕ) :
    tensorMatrix (diagonal p) m = diagonal (fun u => ∏ i, p (u i)) := by
  classical
  ext u v
  by_cases huv : u=v
  · subst v
    simp [tensorMatrix]
  · obtain ⟨i,hi⟩ : ∃ i, u i ≠ v i := by
      by_contra h
      push Not at h
      exact huv (funext h)
    change (∏ j, (diagonal p) (u j) (v j)) =
      diagonal (fun w : Fin m → a => ∏ j, p (w j)) u v
    rw [Matrix.diagonal_apply_ne _ huv]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem tensorMatrix_unitary {a : Type} [Fintype a] [DecidableEq a]
    (U : Mat a) (hU : IsUnitary U) (m : ℕ) : IsUnitary (tensorMatrix U m) := by
  constructor
  · rw [← tensorMatrix_star,← tensorMatrix_mul,hU.1,tensorMatrix_one]
  · rw [← tensorMatrix_star,← tensorMatrix_mul,hU.2,tensorMatrix_one]

theorem tensorMatrix_evolve {a : Type} [Fintype a]
    (U A : Mat a) (m : ℕ) :
    tensorMatrix (evolve U A) m = evolve (tensorMatrix U m) (tensorMatrix A m) := by
  unfold evolve
  rw [tensorMatrix_mul,tensorMatrix_mul,tensorMatrix_star]

theorem traceDistance_unitary {a : Type} [Fintype a] [DecidableEq a]
    (U A B : Mat a) (hU : IsUnitary U) :
    traceDistance (evolve U A) (evolve U B) = traceDistance A B := by
  classical
  have he : evolve U A-evolve U B=evolve U (A-B) := by
    unfold evolve
    noncomm_ring
  unfold traceDistance
  rw [he,ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library]
  have hn : Matrix.traceNorm (evolve U (A-B)) = Matrix.traceNorm (A-B) :=
    by
      have hn := Matrix.traceNorm_unitary_conj (A := A-B) (U := ⟨U, by
        constructor
        · ext i j
          have hh := congrArg (fun D : Mat a => D i j) hU.1
          by_cases hij : i=j <;> simpa [Matrix.one_apply,hij] using hh
        · ext i j
          have hh := congrArg (fun D : Mat a => D i j) hU.2
          by_cases hij : i=j <;> simpa [Matrix.one_apply,hij] using hh⟩)
      simpa only [evolve] using hn
  rw [hn]

end ScheduleLaw.Blueprint.FiniteResidue
