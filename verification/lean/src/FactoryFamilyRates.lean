import FactoryRate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw.Blueprint.FactoryFamilyRates
open History

theorem predecessor_tendsto : Tendsto (fun m : ℕ => m-1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (n+1)] with m hm
  omega

def debit {d : ℕ} (β : ℝ) (τ q : Density (Fin d)) (C : SmallResidueCoding τ) (m : ℕ) : ℝ :=
  let n := m-1
  (energy (tensorHamiltonian (tangentHamiltonian β q) (n+1)) (FactoryRate.decoded C n).matrix +
    (Real.log (C.residue n : ℝ)-Real.log (C.rank n : ℝ))/β+2)/(n+1 : ℝ)

def error {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ) (m : ℕ) : ℝ :=
  C.error (m-1)+1/(m+1 : ℝ)

theorem debit_limit {d : ℕ} (β : ℝ) (τ q : Density (Fin d)) (C : SmallResidueCoding τ) :
    Tendsto (debit β τ q C) atTop (𝓝 (faithfulRelativeEntropy τ.matrix q.matrix/β)) := by
  have h := (FactoryRate.debit_rate β τ q C).comp predecessor_tendsto
  convert h using 1
  funext m
  dsimp [debit]
  ring

theorem error_vanishes {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ) :
    Vanishes (error C) := by
  have h := (C.error_vanishes.comp predecessor_tendsto).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  simpa only [error,add_zero] using h

theorem error_nonneg {d : ℕ} {τ : Density (Fin d)} (C : SmallResidueCoding τ) (m : ℕ) :
    0≤error C m := add_nonneg (C.error_nonneg _) (by positivity)

theorem debit_positive_index {d : ℕ} (β : ℝ) (τ q : Density (Fin d))
    (C : SmallResidueCoding τ) (m : ℕ) (hm : 0 < m) :
    (m : ℝ)*debit β τ q C m =
      energy (tensorHamiltonian (tangentHamiltonian β q) (m-1+1))
        (FactoryRate.decoded C (m-1)).matrix +
      (Real.log (C.residue (m-1) : ℝ)-Real.log (C.rank (m-1) : ℝ))/β+2 := by
  have he : m-1+1=m := by omega
  unfold debit
  dsimp only
  rw [show ((m-1 : ℕ) : ℝ)+1=(m : ℝ) by exact_mod_cast he]
  have hmz : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp [hmz]

end ScheduleLaw.Blueprint.FactoryFamilyRates
