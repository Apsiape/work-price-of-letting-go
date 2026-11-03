import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.BigOperators

/-!
# Energy-conserving lifts and swaps

**The whole-history phase lift (E21).**  Let the external levels `i : ι` carry integer labels `a i` in an additive
group `G` (the lattice `ℤ^r`), with energies `ω (a i)` for an additive map `ω : G →+ ℝ`, and let the phase register
have basis `|b⟩`, `b : G`, with energy `ω b`.  The lift of a matrix `X` is
`L(X) = Σ_{e,f} P_e X P_f ⊗ T_{a_f - a_e}`, with entries
`L(X)((i, b), (j, b')) = X i j` if `b = b' + a j - a i` and `0` otherwise.  We prove:

* `lift_support`: an entry of `L(Y)` from column `(j, b')` to row `(k, c)` vanishes unless `c = b' + a j - a k`, so in
  a product only one intermediate lattice label contributes;
* `lift_mul`: `Σ_k L(X)((i,b),(k,c_k)) L(Y)((k,c_k),(j,b')) = L(XY)((i,b),(j,b'))` with `c_k = b' + a j - a k`;
* `lift_star`, `lift_one`: `L(X^*) = L(X)^*` and `L(1) = 1`;
* `lift_conserves`: every nonzero entry connects states of equal total energy `ω(a i) + ω b = ω(a j) + ω b'`.

**SWAP conserves energy.**  `swap_conserves`: for any Hamiltonian `H` on a port, conjugating `H ⊗ 1 + 1 ⊗ H` by the
swap of the two factors gives back `H ⊗ 1 + 1 ⊗ H` (the delay and thermal-delay devices of Sections 5 and 7).
-/

open Matrix
open scoped Kronecker

namespace Lift

variable {ι G : Type*} [AddCommGroup G] [DecidableEq G]

def lift [DecidableEq ι] (a : ι → G) (X : Matrix ι ι ℂ) : (ι × G) → (ι × G) → ℂ :=
  fun p q => if p.2 = q.2 + a q.1 - a p.1 then X p.1 q.1 else 0

theorem lift_support [DecidableEq ι] (a : ι → G) (Y : Matrix ι ι ℂ) (k j : ι) (c b' : G) (h : lift a Y (k, c) (j, b') ≠ 0) :
    c = b' + a j - a k := by
  unfold lift at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

theorem lift_mul [Fintype ι] [DecidableEq ι] (a : ι → G) (X Y : Matrix ι ι ℂ) (i j : ι) (b b' : G) :
    ∑ k, lift a X (i, b) (k, b' + a j - a k) * lift a Y (k, b' + a j - a k) (j, b')
      = lift a (X * Y) (i, b) (j, b') := by
  unfold lift
  simp only [Matrix.mul_apply]
  have hk : ∀ k, b' + a j - a k + a k - a i = b' + a j - a i := fun k => by abel
  simp only [hk]
  by_cases hb : b = b' + a j - a i
  · simp [hb]
  · simp [hb]

theorem lift_star [DecidableEq ι] (a : ι → G) (X : Matrix ι ι ℂ) (i j : ι) (b b' : G) :
    lift a Xᴴ (i, b) (j, b') = star (lift a X (j, b') (i, b)) := by
  unfold lift
  simp only [conjTranspose_apply]
  by_cases h : b = b' + a j - a i
  · rw [if_pos h, if_pos (by rw [h]; abel)]
  · rw [if_neg h, if_neg (by intro h'; apply h; rw [h']; abel), star_zero]

theorem lift_one [DecidableEq ι] (a : ι → G) (i j : ι) (b b' : G) :
    lift a 1 (i, b) (j, b') = if (i, b) = (j, b') then 1 else 0 := by
  unfold lift
  by_cases hij : i = j
  · subst hij
    by_cases hb : b = b'
    · subst hb; simp
    · simp [hb]
  · simp [hij, Matrix.one_apply_ne hij]

theorem lift_conserves [DecidableEq ι] (a : ι → G) (ω : G →+ ℝ) (X : Matrix ι ι ℂ) (i j : ι) (b b' : G)
    (h : lift a X (i, b) (j, b') ≠ 0) : ω (a i) + ω b = ω (a j) + ω b' := by
  have hb := lift_support a X i j b b' h
  rw [hb, map_sub, map_add]
  ring

theorem swap_conserves {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] (H : Matrix n n R) :
    (H ⊗ₖ (1 : Matrix n n R) + (1 : Matrix n n R) ⊗ₖ H).submatrix Prod.swap Prod.swap
      = H ⊗ₖ (1 : Matrix n n R) + (1 : Matrix n n R) ⊗ₖ H := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [submatrix_apply, Prod.swap_prod_mk, add_apply, kroneckerMap_apply, one_apply]
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl, add_comm]

end Lift

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Lift.lift_support
#print axioms Lift.lift_mul
#print axioms Lift.lift_star
#print axioms Lift.lift_one
#print axioms Lift.lift_conserves
#print axioms Lift.swap_conserves
