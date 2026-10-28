import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Energy-conserving permutations of the constructions

* `Reach`: Stage 2 of the proof of Proposition "A Gibbs-preserving channel that reaches its
  capacity". Basis states `|a⟩_A |z⟩_D |j⟩_C` with `a, z ∈ {0,1}^n` and clock level `j`; energies in
  units of `E` are `|a| + j` (the register `D` has zero Hamiltonian). The swap
  `|a, z, j⟩ ↦ |z, a, j + |a| - |z|⟩` conserves energy and is an involution. On a finite ladder
  `0 ≤ j < top`, acting as the identity on states whose image would leave the ladder, it is still an
  energy-conserving involution of the ladder, hence a permutation; and from the levels
  `n ≤ j < n + L` of a ladder of `2n + L` levels the image never leaves it.
* `Seed`: the seed erasure of Proposition "How large the clock must be" (c). Basis states
  `|j⟩_E |w⟩_W |r⟩_R` with environment level `j` of energy `h j`, a two-level battery of gap `wg`
  and a record cell with a ground level and levels `r_j` of energy `wg + h j - h e0`. The map swapping
  `|j, 1, g⟩` with `|e0, 0, r_j⟩` for every `j`, and acting as the identity elsewhere, is an
  energy-conserving involution.
* `recovery_bijective`: the recovery `|s, a⟩ ↦ |a, s ⊕ a⟩` of the code of (d) is a permutation.
-/

namespace KeepingTime

namespace Reach

variable {n : ℕ}

/-- Number of ones of a bit string. -/
def wt (x : Fin n → Bool) : ℤ := ((Finset.univ.filter (fun i => x i = true)).card : ℤ)

lemma wt_nonneg (x : Fin n → Bool) : 0 ≤ wt x := by unfold wt; positivity

lemma wt_le (x : Fin n → Bool) : wt x ≤ n := by
  unfold wt
  have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

structure St (n : ℕ) where
  a : Fin n → Bool
  z : Fin n → Bool
  j : ℤ

/-- Energy in units of `E`: the register `A` and the clock. -/
def energy (s : St n) : ℤ := wt s.a + s.j

def swap (s : St n) : St n := ⟨s.z, s.a, s.j + wt s.a - wt s.z⟩

theorem swap_energy (s : St n) : energy (swap s) = energy s := by
  simp only [energy, swap]; ring

theorem swap_swap (s : St n) : swap (swap s) = s := by
  cases s
  simp only [swap, St.mk.injEq, true_and]
  ring

def inLadder (top : ℤ) (s : St n) : Prop := 0 ≤ s.j ∧ s.j < top

instance (top : ℤ) (s : St n) : Decidable (inLadder top s) := by unfold inLadder; infer_instance

/-- The gate on a finite ladder: the swap where it stays on the ladder, the identity elsewhere. -/
def gate (top : ℤ) (s : St n) : St n := if inLadder top (swap s) then swap s else s

theorem gate_energy (top : ℤ) (s : St n) : energy (gate top s) = energy s := by
  unfold gate; split_ifs
  · exact swap_energy s
  · rfl

theorem gate_inLadder (top : ℤ) (s : St n) (hs : inLadder top s) : inLadder top (gate top s) := by
  unfold gate; split_ifs with h
  · exact h
  · exact hs

theorem gate_gate (top : ℤ) (s : St n) (hs : inLadder top s) : gate top (gate top s) = s := by
  unfold gate
  by_cases h : inLadder top (swap s)
  · rw [if_pos h, swap_swap, if_pos hs]
  · rw [if_neg h, if_neg h]

/-- On the ladder the gate is a bijection (an involution). -/
theorem gate_injective (top : ℤ) (s t : St n) (hs : inLadder top s) (ht : inLadder top t)
    (h : gate top s = gate top t) : s = t := by
  rw [← gate_gate top s hs, ← gate_gate top t ht, h]

/-- Started on the levels `n ≤ j < n + L`, the swap stays on a ladder of `2n + L` levels. -/
theorem stays (L : ℤ) (s : St n) (h1 : (n : ℤ) ≤ s.j) (h2 : s.j < n + L) :
    inLadder (2 * n + L) (swap s) := by
  have := wt_nonneg s.a; have := wt_nonneg s.z; have := wt_le s.a; have := wt_le s.z
  simp only [inLadder, swap]
  constructor <;> linarith

end Reach

namespace Seed

variable {dE : ℕ}

structure St (dE : ℕ) where
  e : Fin dE
  w : Bool
  r : Option (Fin dE)

/-- Energy: environment level, two-level battery of gap `wg`, record cell with levels
`wg + h j - h e0` above its ground. -/
def energy (h : Fin dE → ℝ) (wg : ℝ) (e0 : Fin dE) (s : St dE) : ℝ :=
  h s.e + (if s.w then wg else 0) + (match s.r with | none => 0 | some j => wg + h j - h e0)

/-- Swap `|j, 1, g⟩` with `|e0, 0, r_j⟩`, identity elsewhere. -/
def erase (e0 : Fin dE) : St dE → St dE
  | ⟨e, true, none⟩ => ⟨e0, false, some e⟩
  | ⟨e, false, some j⟩ => if e = e0 then ⟨j, true, none⟩ else ⟨e, false, some j⟩
  | s => s

theorem erase_energy (h : Fin dE → ℝ) (wg : ℝ) (e0 : Fin dE) (s : St dE) :
    energy h wg e0 (erase e0 s) = energy h wg e0 s := by
  rcases s with ⟨e, _ | _, _ | j⟩
  · rfl
  · by_cases he : e = e0
    · subst he; simp [erase, energy]; ring
    · simp [erase, he]
  · simp [erase, energy]; ring
  · rfl

theorem erase_erase (e0 : Fin dE) (s : St dE) : erase e0 (erase e0 s) = s := by
  rcases s with ⟨e, _ | _, _ | j⟩
  · rfl
  · by_cases he : e = e0
    · subst he; simp [erase]
    · simp [erase, he]
  · simp [erase]
  · rfl

/-- The erasure returns every seed column `|j, 1, g⟩` to the seed level `e0`. -/
theorem erase_returns (e0 j : Fin dE) : (erase e0 ⟨j, true, none⟩).e = e0 := rfl

end Seed

/-- The recovery `|s, a⟩ ↦ |a, s ⊕ a⟩` of the flagged code of (d) is a permutation. -/
theorem recovery_bijective : Function.Bijective (fun p : Bool × Bool => (p.2, xor p.1 p.2)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun q => (xor q.1 q.2, q.1), ?_, ?_⟩
  · rintro ⟨s, a⟩; cases s <;> cases a <;> rfl
  · rintro ⟨x, y⟩; cases x <;> cases y <;> rfl

end KeepingTime

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms KeepingTime.Reach.swap_energy
#print axioms KeepingTime.Reach.swap_swap
#print axioms KeepingTime.Reach.gate_energy
#print axioms KeepingTime.Reach.gate_inLadder
#print axioms KeepingTime.Reach.gate_gate
#print axioms KeepingTime.Reach.gate_injective
#print axioms KeepingTime.Reach.stays
#print axioms KeepingTime.Seed.erase_energy
#print axioms KeepingTime.Seed.erase_erase
#print axioms KeepingTime.Seed.erase_returns
#print axioms KeepingTime.recovery_bijective
