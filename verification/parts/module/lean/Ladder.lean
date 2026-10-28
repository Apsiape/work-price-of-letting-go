import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gibbs ladders: the episode clock (Appendix D, Step 9) and exact flat-rank formation (Appendix E)

**Episode clock.**  Basis states are `(x, j, z, e)`: clock value `x < D` (zero Hamiltonian), ladder level `j ≤ L`
with microstate `z < D^j`, and a two-level battery `e` (excited or ground).  Energies are counted in units of the
battery gap `W_c = β⁻¹ ln D`; level `j` has energy `j`.  An initialized column has the battery excited.  For `j < L`
the swap sends `(x, j, z, excited)` to `(0, j+1, x D^j + z, ground)`.  We prove, for all `D ≥ 1` and `L`, that this
conserves energy, resets the clock, maps valid columns to valid states, is injective, and never lands on an
initialized column, so swapping each column with its image is a full energy-conserving permutation; and that every
ladder level has the same Gibbs weight `D^j e^{-j ln D} = 1`, so the top level (the failure branch) has probability
`1/(L+1)`.

**Flat-rank formation.**  Tiles `j = 0, …, J` with gap `β⁻¹ ln(D/K)` and degeneracy `D^j K^{J-j}` have equal Gibbs
weight `K^J`, and the full flat-`D` block at level `j < J` and the full rank-`K` block at level `j+1` have the same
dimension.
-/

namespace Ladder

structure St where
  x : ℕ
  j : ℕ
  z : ℕ
  excited : Bool
deriving DecidableEq

variable (D L : ℕ)

def Valid (s : St) : Prop := s.x < D ∧ s.j ≤ L ∧ s.z < D ^ s.j

def energy (s : St) : ℕ := s.j + (if s.excited then 1 else 0)

def src (x j z : ℕ) : St := ⟨x, j, z, true⟩

def img (x j z : ℕ) : St := ⟨0, j + 1, x * D ^ j + z, false⟩

theorem energy_img (x j z : ℕ) : energy (img D x j z) = energy (src x j z) := by
  simp [img, src, energy]

theorem clock_reset (x j z : ℕ) : (img D x j z).x = 0 := rfl

theorem valid_img {x j z : ℕ} (hD : 0 < D) (hj : j < L) (h : Valid D L (src x j z)) :
    Valid D L (img D x j z) := by
  obtain ⟨hx, -, hz⟩ := h
  refine ⟨hD, hj, ?_⟩
  simp only [img, src] at hx hz ⊢
  calc x * D ^ j + z < x * D ^ j + D ^ j := by omega
    _ = (x + 1) * D ^ j := by ring
    _ ≤ D * D ^ j := Nat.mul_le_mul_right _ hx
    _ = D ^ (j + 1) := by ring

theorem img_injective {x j z x' j' z' : ℕ} (hD : 0 < D) (h : Valid D L (src x j z))
    (h' : Valid D L (src x' j' z')) (he : img D x j z = img D x' j' z') : x = x' ∧ j = j' ∧ z = z' := by
  obtain ⟨hx, -, hz⟩ := h
  obtain ⟨hx', -, hz'⟩ := h'
  simp only [img, St.mk.injEq, Nat.add_right_cancel_iff, true_and, and_true] at he
  obtain ⟨rfl, hsum⟩ := he
  simp only [src] at hz hz'
  have hpos : 0 < D ^ j := Nat.pow_pos hD
  have hmod : z = z' := by
    have := congrArg (· % D ^ j) hsum
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hz'] using this
  subst hmod
  have : x * D ^ j = x' * D ^ j := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hpos this, rfl, rfl⟩

theorem img_ne_src (x j z x' j' z' : ℕ) : img D x j z ≠ src x' j' z' := by
  simp [img, src]

/-- Every ladder level has the same Gibbs weight. -/
theorem level_weight (j : ℕ) (Dr : ℝ) (hD : 0 < Dr) : Dr ^ j * Real.exp (-(j * Real.log Dr)) = 1 := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
  field_simp

/-- Exact flat-rank formation: equal Gibbs weights of the tiles. -/
theorem tile_weight (j J : ℕ) (hj : j ≤ J) (Dr Kr : ℝ) (hD : 0 < Dr) (hK : 0 < Kr) :
    Real.exp (-(j * Real.log (Dr / Kr))) * (Dr ^ j * Kr ^ (J - j)) = Kr ^ J := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), div_pow]
  have : Kr ^ J = Kr ^ j * Kr ^ (J - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [this]
  field_simp

/-- Exact flat-rank formation: the exchanged blocks have equal dimension. -/
theorem block_dims (Dn Kn j J : ℕ) (hj : j < J) :
    Dn * (Dn ^ j * Kn ^ (J - j)) = Kn * (Dn ^ (j + 1) * Kn ^ (J - (j + 1))) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have h1 : j + t + 1 - j = t + 1 := by omega
  have h2 : j + t + 1 - (j + 1) = t := by omega
  rw [h1, h2]
  ring

end Ladder

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Ladder.energy_img
#print axioms Ladder.clock_reset
#print axioms Ladder.valid_img
#print axioms Ladder.img_injective
#print axioms Ladder.img_ne_src
#print axioms Ladder.level_weight
#print axioms Ladder.tile_weight
#print axioms Ladder.block_dims
