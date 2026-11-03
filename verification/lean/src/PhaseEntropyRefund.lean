import PhaseEntropyLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseEntropyRefund
variable {a : Type} [Fintype a] [DecidableEq a]

/-- The actual polynomial phase dimension is included in the finite
Fannes cost; no dimension-free continuity assertion is used. -/
theorem bound (ρ σ : Density a) (c rank L : ℕ) (hc : 0<c) (K : ℝ)
    (hcard : Fintype.card a=c*(L+4)^rank)
    (h : traceDistance ρ.matrix σ.matrix≤K/(L+1 : ℝ)) :
    |entropy ρ.matrix-entropy σ.matrix|≤PhaseEntropyLimit.modulus c rank K L := by
  have hpos : 0<Fintype.card a := by rw [hcard]; positivity
  have hl0 : 0≤Real.log (Fintype.card a : ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
  have hl : Real.log (Fintype.card a : ℝ)=Real.log c+(rank : ℝ)*Real.log ((L : ℝ)+4) := by
    rw [hcard,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,
      Real.log_mul (by positivity) (by positivity),Real.log_pow]
  have ht0 : 0≤2*traceDistance ρ.matrix σ.matrix := by
    unfold traceDistance
    rw [ClassicalFlag.traceNorm_eq_library]
    exact mul_nonneg (by norm_num) (div_nonneg (Matrix.traceNorm_nonneg _) (by norm_num))
  have ht : 2*traceDistance ρ.matrix σ.matrix≤2*(K/(L+1 : ℝ)) := by linarith
  calc _ ≤ 2*traceDistance ρ.matrix σ.matrix*Real.log (Fintype.card a : ℝ)+
      FiniteFannesScalar.correction (2*traceDistance ρ.matrix σ.matrix) :=
        FiniteFannes.trace_distance_bound ρ σ
       _ ≤ 2*(K/(L+1 : ℝ))*Real.log (Fintype.card a : ℝ)+
          FiniteFannesScalar.correction (2*(K/(L+1 : ℝ))) :=
            add_le_add (mul_le_mul_of_nonneg_right ht hl0) (FiniteFannesScalar.correction_mono ht0 ht)
       _ = _ := by rw [hl]; rfl

end ScheduleLaw.Blueprint.PhaseEntropyRefund
