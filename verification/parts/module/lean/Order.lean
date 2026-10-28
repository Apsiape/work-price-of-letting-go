import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Mul

/-!
# Order costs work, and classical agents (Proposition "Order costs work" and Section 7)

Natural logarithms; entropies are sums of `negMulLog`.

* `cz_conserves`, `cx_conserves`, `cx_needs_degenerate`: the controlled-`Z` gate commutes with every diagonal
  Hamiltonian `H_A ⊗ 1 + 1 ⊗ H_Q`; the controlled-`X` gate commutes with `H_A ⊗ 1 + 1 ⊗ q·1` (degenerate `Q`), and
  not with `1 ⊗ diag(0, e)` for `e ≠ 0` (the one-channel thermal operation of Proposition "Order costs work");
* `masked_device`, `masked_fixed_by_future`, `fop_device`: on all bits, the masked record `M = a ⊕ r` gives
  `Y₂ = b ⊕ a ⊕ r` and `M = Y₂ ⊕ b`; the agent whose memory is `A` gives the same output;
* `masked_mutual_information`: for uniform `a`, `I(M : a) = log 2 - h(p)`;
* `entropy_product`: entropies of independent registers add;
* `agents_table`: the device-entropy changes of the four constructions of the table are `log 2 - h(p)`, `log 2`,
  `2 log 2 - h(p)` and `2 log 2`; keeping the memory in copy-out costs `log 2` more (`copy_out_keep`);
* `single_shot_formation`: for `0 < p < 1/2`, forming one `Bern(p)` bit alone costs `log(2(1-p)) > log 2 - h(p)`.
-/

open Real Matrix
open scoped Kronecker

namespace Order

/-! ## Gates -/

def dg (a0 a1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a0, 0; 0, a1]
def Xm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def P0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def P1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
def Zm : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def CZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := P0 ⊗ₖ 1 + P1 ⊗ₖ Zm
def CX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := P0 ⊗ₖ 1 + P1 ⊗ₖ Xm

theorem cz_conserves (a0 a1 q0 q1 : ℝ) :
    CZ * (dg a0 a1 ⊗ₖ 1 + 1 ⊗ₖ dg q0 q1) = (dg a0 a1 ⊗ₖ 1 + 1 ⊗ₖ dg q0 q1) * CZ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [CZ, dg, P0, P1, Zm, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem cx_conserves (a0 a1 q : ℝ) :
    CX * (dg a0 a1 ⊗ₖ 1 + 1 ⊗ₖ dg q q) = (dg a0 a1 ⊗ₖ 1 + 1 ⊗ₖ dg q q) * CX := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [CX, dg, P0, P1, Xm, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem cx_needs_degenerate (e : ℝ) (he : e ≠ 0) :
    CX * ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ dg 0 e) ≠ ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ dg 0 e) * CX := by
  intro h
  have := congrFun (congrFun h (1, 0)) (1, 1)
  simp [CX, dg, P0, P1, Xm, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, Matrix.one_apply] at this
  exact he this

/-! ## The devices on all bits -/

theorem masked_device (a b r : Bool) :
    let M := xor r a          -- the record after slot 1
    xor b M = xor (xor b a) r := by
  cases a <;> cases b <;> cases r <;> rfl

theorem masked_fixed_by_future (a b r : Bool) : xor r a = xor (xor b (xor r a)) b := by
  cases a <;> cases b <;> cases r <;> rfl

theorem fop_device (a b r : Bool) :
    let mem := a              -- memory that is a function of the past
    xor (xor b mem) r = xor (xor b a) r := by
  cases a <;> cases b <;> cases r <;> rfl

/-! ## Entropies -/

lemma negMulLog_half : negMulLog (1 / 2 : ℝ) = log 2 / 2 := by
  rw [negMulLog, one_div, log_inv]; ring

theorem entropy_uniform_bit : negMulLog (1 / 2 : ℝ) + negMulLog (1 / 2) = log 2 := by
  rw [negMulLog_half]; ring

theorem entropy_bern (p : ℝ) : negMulLog (1 - p) + negMulLog p = binEntropy p := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]; ring

theorem entropy_product {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → ℝ) (q : κ → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    ∑ i, ∑ j, negMulLog (p i * q j) = ∑ i, negMulLog (p i) + ∑ j, negMulLog (q j) := by
  simp only [negMulLog_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => q j * negMulLog (p i))]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hp, hq, one_mul]

/-- `I(M : a) = H(a) + H(M) - H(a, M)` for uniform `a` and `M = a ⊕ r`, `r ~ Bern(p)`. -/
theorem masked_mutual_information (p : ℝ) :
    (negMulLog (1 / 2) + negMulLog (1 / 2))
      + (negMulLog (1 / 2 * (1 - p) + 1 / 2 * p) + negMulLog (1 / 2 * p + 1 / 2 * (1 - p)))
      - (negMulLog (1 / 2 * (1 - p)) + negMulLog (1 / 2 * p) + negMulLog (1 / 2 * p) + negMulLog (1 / 2 * (1 - p)))
      = log 2 - binEntropy p := by
  have e1 : (1 / 2 : ℝ) * (1 - p) + 1 / 2 * p = 1 / 2 := by ring
  have e2 : (1 / 2 : ℝ) * p + 1 / 2 * (1 - p) = 1 / 2 := by ring
  rw [e1, e2, negMulLog_mul, negMulLog_mul, negMulLog_half, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- Entropy of a uniform bit (a mixed cell, the record after slot 1, or the memory `A`). -/
noncomputable def Hu : ℝ := negMulLog (1 / 2 : ℝ) + negMulLog (1 / 2)
/-- Entropy of the coin `Bern(p)`. -/
noncomputable def Hb (p : ℝ) : ℝ := negMulLog (1 - p) + negMulLog p
/-- Entropy of a blank. -/
noncomputable def blank : ℝ := negMulLog (1 : ℝ)

lemma Hu_eq : Hu = log 2 := entropy_uniform_bit
lemma Hb_eq (p : ℝ) : Hb p = binEntropy p := entropy_bern p
lemma blank_eq : blank = 0 := negMulLog_one

/-- The four entries of the table, as entropy increases of everything the device holds (after minus before).
In place: the masked record turns the coin into a uniform bit; the agent whose memory is `A` adds a uniform bit and
keeps its coin.  Copy-out: both incoming mixed cells are kept and the memory register leaves as the `Y₂` cell; the
coin stays with the agent whose memory is a function of the past.  That agent pays `h(p)` more in both
interfaces. -/
theorem agents_table (p : ℝ) :
    Hu - Hb p = log 2 - binEntropy p ∧ (Hu + Hb p) - (blank + Hb p) = log 2 ∧
    (Hu + Hu) - (Hb p + blank) = 2 * log 2 - binEntropy p ∧ (Hu + Hu + Hb p) - (blank + blank + Hb p) = 2 * log 2 ∧
    ((Hu + Hb p) - (blank + Hb p)) - (Hu - Hb p) = binEntropy p ∧
    ((Hu + Hu + Hb p) - (blank + blank + Hb p)) - ((Hu + Hu) - (Hb p + blank)) = binEntropy p := by
  rw [Hu_eq, Hb_eq, blank_eq]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- In copy-out, keeping the memory and writing `Y₂` on a fresh blank costs `log 2` more, for both agents. -/
theorem copy_out_keep (p : ℝ) :
    ((Hu + Hu + Hu) - (Hb p + blank + blank)) - ((Hu + Hu) - (Hb p + blank)) = log 2 ∧
      ((Hu + Hu + Hu + Hb p) - (blank + blank + blank + Hb p)) - ((Hu + Hu + Hb p) - (blank + blank + Hb p))
        = log 2 := by
  rw [Hu_eq, Hb_eq, blank_eq]
  refine ⟨by ring, by ring⟩

theorem single_shot_formation (p : ℝ) (h0 : 0 < p) (h1 : p < 1 / 2) :
    log 2 - binEntropy p < log (2 * (1 - p)) := by
  have hq : 0 < 1 - p := by linarith
  rw [log_mul (by norm_num) hq.ne', binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
  have hlt : log p < log (1 - p) := log_lt_log h0 (by linarith)
  nlinarith [mul_lt_mul_of_pos_left hlt h0]

end Order

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms Order.cz_conserves
#print axioms Order.cx_conserves
#print axioms Order.cx_needs_degenerate
#print axioms Order.masked_device
#print axioms Order.masked_fixed_by_future
#print axioms Order.fop_device
#print axioms Order.negMulLog_half
#print axioms Order.entropy_uniform_bit
#print axioms Order.entropy_bern
#print axioms Order.entropy_product
#print axioms Order.masked_mutual_information
#print axioms Order.Hu_eq
#print axioms Order.Hb_eq
#print axioms Order.blank_eq
#print axioms Order.agents_table
#print axioms Order.copy_out_keep
#print axioms Order.single_shot_formation
