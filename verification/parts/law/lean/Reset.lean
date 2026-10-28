import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Nat

/-!
# The shell-stock reset (Appendix "Release rank", construction)

Basis states are `(x, j, z, b)`: memory value `x < K`, stock shell `j ≤ J` with microstate
`z < K^j`, and battery `b`, either `none` (ground, energy 0) or `some y` (one of `K` excited
levels of energy `w`).  Energies are counted in units of `w`.  Initialized columns have the
battery in `some 0`.  The reset sends the column `(x, j, z, some 0)` to

* `(0, j+1, x K^j + z, none)` if `j < J`,
* `(0, J, z, some x)`          if `j = J`.

We prove, for all `K ≥ 1` and `J`, that this assignment conserves energy, returns the memory to
`0`, maps valid columns to valid states, is injective, and meets the initialized columns only in
fixed points.  Hence swapping each column with its image, and acting as the identity elsewhere,
is a full energy-conserving permutation that returns the memory on every initialized branch.
-/

namespace Reset

structure St where
  x : ℕ
  j : ℕ
  z : ℕ
  b : Option ℕ
deriving DecidableEq

variable (K J : ℕ)

/-- Valid basis states. -/
def Valid (s : St) : Prop :=
  s.x < K ∧ s.j ≤ J ∧ s.z < K ^ s.j ∧ ∀ y, s.b = some y → y < K

/-- Energy in units of `w`. -/
def energy (s : St) : ℕ := s.j + (if s.b = none then 0 else 1)

/-- An initialized column. -/
def src (x j z : ℕ) : St := ⟨x, j, z, some 0⟩

/-- Its image under the reset. -/
def img (x j z : ℕ) : St := if j < J then ⟨0, j + 1, x * K ^ j + z, none⟩ else ⟨0, J, z, some x⟩

theorem energy_img {x j z : ℕ} (hj : j ≤ J) : energy (img K J x j z) = energy (src x j z) := by
  by_cases h : j < J
  · simp [img, src, energy, h]
  · have : j = J := le_antisymm hj (not_lt.mp h)
    subst this
    simp [img, src, energy]

theorem memory_img (x j z : ℕ) : (img K J x j z).x = 0 := by
  unfold img; split_ifs <;> rfl

theorem valid_img {x j z : ℕ} (hK : 0 < K) (h : Valid K J (src x j z)) : Valid K J (img K J x j z) := by
  simp only [Valid, src] at h
  obtain ⟨hx, hj, hz, -⟩ := h
  by_cases hlt : j < J
  · simp only [Valid, img, hlt, if_true]
    refine ⟨hK, hlt, ?_, by simp⟩
    calc x * K ^ j + z < x * K ^ j + K ^ j := by omega
      _ = (x + 1) * K ^ j := by ring
      _ ≤ K * K ^ j := Nat.mul_le_mul_right _ hx
      _ = K ^ (j + 1) := by ring
  · have : j = J := le_antisymm hj (not_lt.mp hlt)
    subst this
    simp only [Valid, img, hlt, if_false]
    exact ⟨hK, le_rfl, hz, by intro y hy; simp at hy; omega⟩

/-- Distinct valid initialized columns have distinct images. -/
theorem img_injective {x j z x' j' z' : ℕ} (hK : 0 < K)
    (h : Valid K J (src x j z)) (h' : Valid K J (src x' j' z'))
    (he : img K J x j z = img K J x' j' z') : x = x' ∧ j = j' ∧ z = z' := by
  simp only [Valid, src] at h h'
  obtain ⟨hx, hj, hz, -⟩ := h
  obtain ⟨hx', hj', hz', -⟩ := h'
  by_cases h1 : j < J <;> by_cases h2 : j' < J <;> simp only [img, h1, h2, if_true, if_false] at he
  · simp only [St.mk.injEq, Nat.add_right_cancel_iff, true_and] at he
    obtain ⟨rfl, hsum, -⟩ := he
    have hpos : 0 < K ^ j := Nat.pow_pos hK
    have hmod : z = z' := by
      have := congrArg (· % K ^ j) hsum
      simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hz'] using this
    subst hmod
    have : x * K ^ j = x' * K ^ j := by omega
    exact ⟨Nat.eq_of_mul_eq_mul_right hpos this, rfl, rfl⟩
  · simp at he
  · simp at he
  · simp only [St.mk.injEq, Option.some.injEq, true_and] at he
    obtain ⟨hzz, hxx⟩ := he
    exact ⟨hxx, by omega, hzz⟩

/-- An image is an initialized column only when it is the column itself (a fixed point). -/
theorem img_eq_src {x j z x' j' z' : ℕ} (hj : j ≤ J)
    (he : img K J x j z = src x' j' z') : img K J x j z = src x j z := by
  by_cases h1 : j < J
  · simp [img, src, h1] at he
  · have : j = J := le_antisymm hj (not_lt.mp h1)
    subst this
    simp only [img, src, h1, if_false, St.mk.injEq, Option.some.injEq] at he ⊢
    simp_all

end Reset

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Reset.energy_img
#print axioms Reset.memory_img
#print axioms Reset.valid_img
#print axioms Reset.img_injective
#print axioms Reset.img_eq_src
