import FactoryBattery
import FactorySupport
import FactoryEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryPreparedEnergy
open History

theorem diagonal_energy {a : Type} [Fintype a] [DecidableEq a]
    (E : a → ℝ) (ρ : Mat a) :
    energy (diagonal (fun j => (E j : ℂ))) ρ=∑ j,E j*(ρ j j).re := by
  simp only [energy,diagonal_mul,Matrix.trace,Matrix.diag_apply,Complex.re_sum,
    Complex.re_ofReal_mul]

theorem energy_basis {a : Type} [Fintype a]
    (U A ρ : Mat a) : energy (evolve U A) ρ=energy A (evolve Uᴴ ρ) := by
  rw [energy_pullback,conjTranspose_conjTranspose]
  rfl

/-- A high-probability eigenprojection controls the actual mean energy
linearly in failure, including coherent inputs. -/
theorem preparation_error {a : Type} [Fintype a] [DecidableEq a]
    (U : Mat a) (hU : IsUnitary U) (E : a → ℝ) (i : a)
    (ρ : Density a) (A ε : ℝ) (hA : 0≤A) (hgap : ∀ j,|E j-E i|≤A)
    (hp : 1-ε≤energy (evolve U (diagonal (fun j => if j=i then 1 else 0))) ρ.matrix) :
    |energy (evolve U (diagonal (fun j => (E j : ℂ)))) ρ.matrix-E i|≤A*ε := by
  let σ : Density a := ⟨evolve Uᴴ ρ.matrix,
    ρ.positive.mul_mul_conjTranspose_same Uᴴ,
    evolve_trace_one _ _ (FiniteFlat.adjoint_unitary hU) ρ.normalized⟩
  have hprob : energy (evolve U (diagonal (fun j => if j=i then 1 else 0))) ρ.matrix=
      (σ.matrix i i).re := by
    rw [energy_basis]
    simp [energy,diagonal_mul,Matrix.trace,Matrix.diag_apply,σ]
  rw [hprob] at hp
  rw [energy_basis,diagonal_energy]
  have hm := battery_tail_controls_mean (fun j => (σ.matrix j j).re) E (E i)
    (FactoryBattery.diagonal_nonneg σ) (FactoryBattery.diagonal_sum σ)
  have ht := FactoryBattery.absolute_tail σ E i A hgap
  exact hm.trans (ht.trans (mul_le_mul_of_nonneg_left (by linarith) hA))

/-- The two output approximations give the missing failure-column energy
term when the pump is calibrated using the ideal decoded coding state. -/
theorem output_energy_error {a : Type} [Fintype a] [DecidableEq a]
    (H A B T : Mat a) (M ε f : ℝ) (hM : 0≤M) (hH : ‖H‖≤M)
    (hε : 0≤ε) (hf : 0≤f) (hA : traceDistance A T≤ε+f)
    (hB : traceDistance B T≤ε) :
    |energy H A-energy H B|≤2*M*(2*ε+f) := by
  have ha := FactoryEnergy.energy_distance H A T
  have hb := FactoryEnergy.energy_distance H B T
  have hdA : 0≤traceDistance A T :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by norm_num)
  have hdB : 0≤traceDistance B T :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by norm_num)
  have ha' : |energy H A-energy H T|≤2*M*(ε+f) :=
    ha.trans ((mul_le_mul_of_nonneg_right (by linarith : 2*‖H‖≤2*M) hdA).trans
      (mul_le_mul_of_nonneg_left hA (by positivity)))
  have hb' : |energy H B-energy H T|≤2*M*ε :=
    hb.trans ((mul_le_mul_of_nonneg_right (by linarith : 2*‖H‖≤2*M) hdB).trans
      (mul_le_mul_of_nonneg_left hB (by positivity)))
  have ht : |energy H A-energy H B|≤
      |energy H A-energy H T|+|energy H B-energy H T| := by
    simpa only [abs_sub_comm (energy H T) (energy H B)] using
      abs_sub_le (energy H A) (energy H T) (energy H B)
  linarith

end ScheduleLaw.Blueprint.FactoryPreparedEnergy
