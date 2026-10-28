import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The no-programming step (Proposition "How large the clock must be" (d))

Two programs `p`, `q` with overlap `f` give Stinespring isometries with `W_p^* W_q = f I`; if the
channels are close to `I` and to a unitary with eigenvalues `e^{± i φ/2}`, then `f I` is close to
`z U` for some complex `z`. The step used in the manuscript is the scalar inequality

  `max(|f - z e^{iφ/2}|, |f - z e^{-iφ/2}|) ≥ f sin(φ/2)`  for `f ≥ 0`, all complex `z` and real `φ`,

proved here as `eigenphase`. Its proof: multiplying by the unimodular `e^{∓iφ/2}` turns the two
distances into `|f e^{∓iφ/2} - z|`, whose sum is at least `|f e^{iφ/2} - f e^{-iφ/2}| = 2f|sin(φ/2)|`.
-/

namespace KeepingTime

open Complex

lemma exp_sub_exp_neg (θ : ℝ) :
    exp ((θ : ℂ) * I) - exp (-((θ : ℂ) * I)) = 2 * (Real.sin θ : ℂ) * I := by
  have h1 : exp (-((θ : ℂ) * I)) = exp (((-θ : ℝ) : ℂ) * I) := by push_cast; ring_nf
  rw [h1, exp_mul_I, exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

theorem eigenphase (f φ : ℝ) (z : ℂ) (hf : 0 ≤ f) :
    f * Real.sin (φ / 2) ≤
      max ‖(f : ℂ) - z * exp (((φ / 2 : ℝ) : ℂ) * I)‖ ‖(f : ℂ) - z * exp (-(((φ / 2 : ℝ) : ℂ) * I))‖ := by
  set u := exp (((φ / 2 : ℝ) : ℂ) * I) with hu_def
  set v := exp (-(((φ / 2 : ℝ) : ℂ) * I)) with hv_def
  have huv : u * v = 1 := by rw [hu_def, hv_def, ← exp_add]; simp
  have hvu : v * u = 1 := by rw [mul_comm]; exact huv
  have hu : ‖u‖ = 1 := norm_exp_ofReal_mul_I _
  have hv : ‖v‖ = 1 := by
    rw [hv_def, show -(((φ / 2 : ℝ) : ℂ) * I) = (((-(φ / 2)) : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have h1 : ‖(f : ℂ) - z * u‖ = ‖(f : ℂ) * v - z‖ := by
    calc ‖(f : ℂ) - z * u‖ = ‖((f : ℂ) - z * u) * v‖ := by rw [norm_mul, hv, mul_one]
      _ = ‖(f : ℂ) * v - z‖ := by rw [sub_mul, mul_assoc, huv, mul_one]
  have h2 : ‖(f : ℂ) - z * v‖ = ‖(f : ℂ) * u - z‖ := by
    calc ‖(f : ℂ) - z * v‖ = ‖((f : ℂ) - z * v) * u‖ := by rw [norm_mul, hu, mul_one]
      _ = ‖(f : ℂ) * u - z‖ := by rw [sub_mul, mul_assoc, hvu, mul_one]
  have htri : ‖(f : ℂ) * u - (f : ℂ) * v‖ ≤ ‖(f : ℂ) * u - z‖ + ‖(f : ℂ) * v - z‖ := by
    calc ‖(f : ℂ) * u - (f : ℂ) * v‖ = ‖((f : ℂ) * u - z) - ((f : ℂ) * v - z)‖ := by ring_nf
      _ ≤ ‖(f : ℂ) * u - z‖ + ‖(f : ℂ) * v - z‖ := norm_sub_le _ _
  have hdiff : (f : ℂ) * u - (f : ℂ) * v = 2 * (f : ℂ) * (Real.sin (φ / 2) : ℂ) * I := by
    rw [← mul_sub, hu_def, hv_def, exp_sub_exp_neg]
    ring
  have hnorm : ‖(f : ℂ) * u - (f : ℂ) * v‖ = 2 * f * |Real.sin (φ / 2)| := by
    rw [hdiff, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf]
    norm_num
  have hs : f * Real.sin (φ / 2) ≤ f * |Real.sin (φ / 2)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hf
  rw [h1, h2]
  have hmax1 := le_max_left ‖(f : ℂ) * v - z‖ ‖(f : ℂ) * u - z‖
  have hmax2 := le_max_right ‖(f : ℂ) * v - z‖ ‖(f : ℂ) * u - z‖
  linarith

/-- The bound is attained: with `θ = φ/2` and `z = f cos θ`, `|f - z e^{iθ}| = f |sin θ|` (and the
same for `e^{-iθ}` by symmetry). -/
theorem eigenphase_attained (f θ : ℝ) (hf : 0 ≤ f) :
    ‖(f : ℂ) - ((f * Real.cos θ : ℝ) : ℂ) * exp ((θ : ℂ) * I)‖ = f * |Real.sin θ| := by
  have h1 : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  have e : (f : ℂ) - ((f * Real.cos θ : ℝ) : ℂ) * exp ((θ : ℂ) * I) =
      ((f * Real.sin θ ^ 2 : ℝ) : ℂ) + ((-(f * Real.cos θ * Real.sin θ)) : ℝ) * I := by
    rw [exp_mul_I]
    push_cast
    linear_combination (-(f : ℂ)) * h1
  have hs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hsq : ‖(f : ℂ) - ((f * Real.cos θ : ℝ) : ℂ) * exp ((θ : ℂ) * I)‖ ^ 2 = (f * |Real.sin θ|) ^ 2 := by
    rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
    calc (f * Real.sin θ ^ 2) ^ 2 + (-(f * Real.cos θ * Real.sin θ)) ^ 2
        = f ^ 2 * Real.sin θ ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = (f * |Real.sin θ|) ^ 2 := by rw [hs, mul_pow, sq_abs]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end KeepingTime

-- Axiom audit: every theorem must depend only on propext, Classical.choice and Quot.sound.
#print axioms KeepingTime.eigenphase
#print axioms KeepingTime.eigenphase_attained
