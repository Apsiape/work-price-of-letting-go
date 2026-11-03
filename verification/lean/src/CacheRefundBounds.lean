import FiniteFannes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.CacheRefundBounds
open History

def modulus (d : ℕ) (ε : ℝ) : ℝ :=
  2*ε*(1+Real.log d)+FiniteFannesScalar.correction (2*ε)

theorem entropy_refund {d n : ℕ} (hd : 0<d)
    (ρ σ : Density (Fin (n+1) × (Fin n → Fin d))) (ε : ℝ) (hε : 0  ≤  ε)
    (h : traceDistance ρ.matrix σ.matrix  ≤  ε/(n+1 : ℝ)) :
    |entropy ρ.matrix-entropy σ.matrix|  ≤  modulus d ε := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hdR : 0<(d : ℝ) := by exact_mod_cast hd
  have hlD : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hc : (Fintype.card (Fin (n+1) × (Fin n → Fin d)) : ℝ) = (n+1 : ℝ)*(d : ℝ)^n := by simp
  have hl : Real.log (Fintype.card (Fin (n+1) × (Fin n → Fin d)) : ℝ)  ≤ 
      (n+1 : ℝ)*(1+Real.log (d : ℝ)) := by
    rw [hc,Real.log_mul (by positivity) (by positivity),Real.log_pow]
    have hm := Real.log_le_sub_one_of_pos (show 0<(n+1 : ℝ) by positivity)
    nlinarith
  have hl0 : 0 ≤ Real.log (Fintype.card (Fin (n+1) × (Fin n → Fin d)) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=Fin (n+1) × (Fin n → Fin d)))
  have ht0 : 0 ≤ 2*traceDistance ρ.matrix σ.matrix := by
    rw [traceDistance,ClassicalFlag.traceNorm_eq_library]
    exact mul_nonneg (by norm_num) (div_nonneg (Matrix.traceNorm_nonneg _) (by norm_num))
  have he : ε/(n+1 : ℝ) ≤ ε := div_le_self hε (by norm_cast; omega)
  have ht : 2*traceDistance ρ.matrix σ.matrix ≤ 2*ε := by linarith
  have hp : 2*traceDistance ρ.matrix σ.matrix*
      Real.log (Fintype.card (Fin (n+1) × (Fin n → Fin d)) : ℝ)  ≤  2*ε*(1+Real.log (d : ℝ)) := by
    calc _  ≤  2*(ε/(n+1 : ℝ))*Real.log (Fintype.card (Fin (n+1) × (Fin n → Fin d)) : ℝ) :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) hl0
         _  ≤  2*(ε/(n+1 : ℝ))*((n+1 : ℝ)*(1+Real.log (d : ℝ))) :=
           mul_le_mul_of_nonneg_left hl (by positivity)
         _ = _ := by field_simp; <;> ring
  exact (FiniteFannes.trace_distance_bound ρ σ).trans
    (add_le_add hp (FiniteFannesScalar.correction_mono ht0 ht))

theorem energy_refund {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Density a) (H : Mat a) (n : ℕ) (K ε : ℝ) (hK : 0  ≤  K) (hε : 0  ≤  ε)
    (hH : ‖H‖  ≤  (n+1 : ℝ)*K) (h : traceDistance ρ.matrix σ.matrix  ≤  ε/(n+1 : ℝ)) :
    |energy H ρ.matrix-energy H σ.matrix|  ≤  2*K*ε := by
  have ht0 : 0 ≤ traceDistance ρ.matrix σ.matrix := by
    rw [traceDistance,ClassicalFlag.traceNorm_eq_library]
    exact div_nonneg (Matrix.traceNorm_nonneg _) (by norm_num)
  calc _  ≤  2*‖H‖*traceDistance ρ.matrix σ.matrix := FactoryEnergy.energy_distance H ρ.matrix σ.matrix
       _  ≤  2*((n+1 : ℝ)*K)*(ε/(n+1 : ℝ)) :=
         mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num)) h ht0 (by positivity)
       _ = _ := by field_simp; <;> ring

theorem modulus_vanishes (d : ℕ) (err : ℕ → ℝ) (h : Vanishes err) :
    Vanishes (fun n => modulus d (err n)) := by
  have ht : Tendsto (fun n => 2*err n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul h
  have hc := FiniteFannesScalar.correction_tendsto_zero.comp ht
  simpa only [modulus,zero_mul,zero_add] using (ht.mul_const (1+Real.log d)).add hc

end ScheduleLaw.Blueprint.CacheRefundBounds
