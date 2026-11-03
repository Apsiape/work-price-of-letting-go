import BlueprintContracts
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace ScheduleLaw.Blueprint.W2

abbrev RealSequence := lp (fun _ : ℤ => ℝ) 2

def sequenceShift (u : RealSequence) (k : ℤ) : RealSequence :=
  ⟨fun x => u (x-k), by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    exact (Equiv.subRight k).summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩

theorem sequence_norm_sq (u : RealSequence) : ‖u‖^2=∑' x : ℤ,(u x)^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using h

theorem sequenceShift_norm (u : RealSequence) (k : ℤ) : ‖sequenceShift u k‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sequence_norm_sq,sequence_norm_sq]
  exact (Equiv.subRight k).tsum_eq (fun x : ℤ => (u x)^2)

theorem sequenceShift_sub_norm_nat (u : RealSequence) (n : ℕ) :
    ‖sequenceShift u (n : ℤ)-u‖ ≤ (n : ℝ)*‖sequenceShift u 1-u‖ := by
  induction n with
  | zero =>
    have hzero : sequenceShift u 0=u := by apply lp.ext; funext x; change u (x-0)=u x; rw [sub_zero]
    simp [hzero]
  | succ n ih =>
    have heq : sequenceShift u ((n+1 : ℕ) : ℤ)-u =
        sequenceShift (sequenceShift u (n : ℤ)-u) 1 + (sequenceShift u 1-u) := by
      apply lp.ext
      funext x
      change u (x-((n+1 : ℕ) : ℤ))-u x =
        (u (x-1-(n : ℤ))-u (x-1))+(u (x-1)-u x)
      have hi : x-1-(n : ℤ)=x-((n+1 : ℕ) : ℤ) := by omega
      rw [hi]
      ring
    calc ‖sequenceShift u ((n+1 : ℕ) : ℤ)-u‖
        = ‖sequenceShift (sequenceShift u (n : ℤ)-u) 1+(sequenceShift u 1-u)‖ := congrArg norm heq
      _ ≤ ‖sequenceShift (sequenceShift u (n : ℤ)-u) 1‖+‖sequenceShift u 1-u‖ := norm_add_le _ _
      _ = ‖sequenceShift u (n : ℤ)-u‖+‖sequenceShift u 1-u‖ := by rw [sequenceShift_norm]
      _ ≤ (n : ℝ)*‖sequenceShift u 1-u‖+‖sequenceShift u 1-u‖ := by linarith
      _ = ((n+1 : ℕ) : ℝ)*‖sequenceShift u 1-u‖ := by push_cast; ring

theorem sequenceShift_sub_norm_neg (u : RealSequence) (k : ℤ) :
    ‖sequenceShift u (-k)-u‖=‖sequenceShift u k-u‖ := by
  have heq : sequenceShift u (-k)-u = -sequenceShift (sequenceShift u k-u) (-k) := by
    apply lp.ext
    funext x
    change u (x-(-k))-u x = -(u (x-(-k)-k)-u (x-(-k)))
    have hi : x-(-k)-k=x := by omega
    rw [hi]
    ring
  rw [heq,norm_neg,sequenceShift_norm]

theorem sequenceShift_sub_norm (u : RealSequence) (k : ℤ) :
    ‖sequenceShift u k-u‖ ≤ (|k| : ℤ)*‖sequenceShift u 1-u‖ := by
  cases k with
  | ofNat n => simpa using sequenceShift_sub_norm_nat u n
  | negSucc n =>
    have hk : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
    rw [hk,sequenceShift_sub_norm_neg,abs_neg]
    rw [abs_of_nonneg (Int.natCast_nonneg (n+1))]
    exact sequenceShift_sub_norm_nat u (n+1)

theorem sequenceShift_inner (u v : RealSequence) (k : ℤ) :
    inner ℝ (sequenceShift u k) v = inner ℝ u (sequenceShift v (-k)) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  have h := (Equiv.subRight k).tsum_eq (fun x : ℤ => u x * v (x+k))
  simpa only [Real.inner_apply,sequenceShift,Equiv.subRight_apply,sub_add_cancel,
    sub_neg_eq_add] using h

end ScheduleLaw.Blueprint.W2
