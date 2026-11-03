import PhaseVectorDistance
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhaseReferenceBound
open PhaseVectorDistance
variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]

theorem vector_matrix_norm (M : Matrix a b ℂ) :
    ‖vector (fun x : a × b => M x.1 x.2)‖=‖M‖ := by
  rw [EuclideanSpace.norm_eq,Matrix.frobenius_norm_def]
  simp only [vector,PiLp.toLp_apply,Fintype.sum_prod_type,Real.rpow_two,Real.sqrt_eq_rpow]

theorem column_bound (E : Matrix a b ℂ) (ε : ℝ) (hε : 0≤ε) (hb : 0<Fintype.card b)
    (hE : ∀ j,‖vector (fun i => E i j)‖≤ε) : ‖E‖≤(Fintype.card b : ℝ)*ε := by
  have hs : ‖E‖^2=∑ j,‖vector (fun i => E i j)‖^2 := by
    rw [← vector_matrix_norm,EuclideanSpace.norm_sq_eq]
    simp only [vector,PiLp.toLp_apply,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (EuclideanSpace.norm_sq_eq (vector (fun i => E i j))).symm
  have hsq : ‖E‖^2 ≤ (Fintype.card b : ℝ)*ε^2 := by
    rw [hs]
    calc _ ≤ ∑ _ : b,ε^2 := Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hE j) 2)
         _ = _ := by simp
  have hq : (1 : ℝ)≤Fintype.card b := by exact_mod_cast hb
  have hh : (Fintype.card b : ℝ)*ε^2≤((Fintype.card b : ℝ)*ε)^2 := by
    nlinarith [mul_nonneg (show 0≤(Fintype.card b : ℝ)^2-Fintype.card b by nlinarith) (sq_nonneg ε)]
  nlinarith [norm_nonneg E,mul_nonneg (Nat.cast_nonneg (Fintype.card b)) hε]

/-- A column estimate controls every reference dimension through the
Frobenius multiplication inequality; no dimension factor for c occurs. -/
theorem uniform_reference (E : Matrix a b ℂ) (ψ : Matrix b c ℂ)
    (ε : ℝ) (hε : 0≤ε) (hb : 0<Fintype.card b)
    (hE : ∀ j,‖vector (fun i => E i j)‖≤ε)
    (hψ : ‖vector (fun x : b × c => ψ x.1 x.2)‖=1) :
    ‖vector (fun x : a × c => (E*ψ) x.1 x.2)‖≤(Fintype.card b : ℝ)*ε := by
  rw [vector_matrix_norm]
  have hψ' : ‖ψ‖=1 := by rw [← vector_matrix_norm]; exact hψ
  exact (Matrix.frobenius_norm_mul E ψ).trans (by
    rw [hψ',mul_one]
    exact column_bound E ε hε hb hE)

end ScheduleLaw.Blueprint.PhaseReferenceBound
