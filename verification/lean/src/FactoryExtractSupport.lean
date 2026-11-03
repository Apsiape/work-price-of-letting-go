import FactorySupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactorySupport
open History

/-- Extraction uses the entire retained support, including its coding residue.
 It makes no independence assumption about that support and a reference. -/
theorem extract_support {d : ℕ} (hd : 0<d) (β : ℝ) (hβ : 0<β)
    (P : Mat (Fin d)) (hP : P.IsHermitian) (hPi : P*P=P)
    (k : ℕ) (hk : 0<k) (htr : P.trace=(k : ℂ)) (f : ℝ) (hf : 0<f) :
    ∃ C : SupportConverter β (FiniteFlat.zeroHamiltonian d) (Real.log ((d : ℝ)/k)/β-1),
      ∀ z (ρ : Density (Fin d × Fin z)), (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix →
      1-f ≤ energy (((1 : Mat (Fin d)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  have hb : boltzmann β (FiniteFlat.zeroHamiltonian d)=(1 : Mat (Fin d)) := by
    rw [SupportBasis.boltzmann_in_basis β (FiniteFlat.zeroHamiltonian d) 1
      (by constructor <;> simp) (fun _ => 0) (by simp [FiniteFlat.zeroHamiltonian,evolve])]
    simp [evolve]
  have hZP : energy P (boltzmann β (FiniteFlat.zeroHamiltonian d))=(k : ℝ) := by
    rw [hb]
    simp [energy,htr]
  have hZQ : energy (1 : Mat (Fin d)) (boltzmann β (FiniteFlat.zeroHamiltonian d))=(d : ℝ) := by
    rw [hb]
    simp [energy]
  have hx : Real.log ((d : ℝ)/k)/β-1 <
      Real.log (energy (1 : Mat (Fin d)) (boltzmann β (FiniteFlat.zeroHamiltonian d))/
        energy P (boltzmann β (FiniteFlat.zeroHamiltonian d)))/β := by
    rw [hZP,hZQ]
    linarith
  exact energy_shell_support_conversion hd β hβ (FiniteFlat.zeroHamiltonian d) P 1 hP hPi
    (by simp [Matrix.IsHermitian]) (by simp) (by simp [FiniteFlat.zeroHamiltonian])
    (by simp) (by rw [hZP]; exact_mod_cast hk) (by rw [hZQ]; exact_mod_cast hd) _ f hx hf

end ScheduleLaw.Blueprint.FactorySupport
