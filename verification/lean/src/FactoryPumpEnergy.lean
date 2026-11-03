import FactoryPhysicalHamiltonian
import FactoryInitializedFlags

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPumpEnergy
open History FactoryRegisters FactoryRegisterOutput FactoryPhysicalHamiltonian

theorem placed_energy {a u v : Type} [Fintype a] [Fintype u] [Fintype v]
    [DecidableEq a] [DecidableEq u] [DecidableEq v]
    (e : a ≃ u × v) (H : Mat u) (K : Mat v) (ρ : Mat a) :
    energy ((sumH H K).submatrix e e) ρ =
      energy H (partialRight (ρ.submatrix e.symm e.symm)) +
      energy K (partialLeft (ρ.submatrix e.symm e.symm)) := by
  have he : ((sumH H K).submatrix e e).submatrix e.symm e.symm=sumH H K := by
    ext i j
    simp only [submatrix_apply,Equiv.apply_symm_apply]
  rw [← energy_reindex e.symm,he,sumH,energy_add,energy_kron_one,energy_one_kron]

theorem placed_change {a u v : Type} [Fintype a] [Fintype u] [Fintype v]
    [DecidableEq a] [DecidableEq u] [DecidableEq v]
    (e : a ≃ u × v) (U H : Mat u) (K : Mat v) (hU : IsUnitary U) (ρ : Mat a) :
    energy ((sumH H K).submatrix e e) (evolve (FactoryPlacement.place e U) ρ) -
        energy ((sumH H K).submatrix e e) ρ =
      energy H (evolve U (marginal e ρ))-energy H (marginal e ρ) := by
  rw [placed_energy,placed_energy,FactoryPlacement.rest_invariant e U hU ρ,
    FactoryPlacement.operated_marginal e U ρ]
  dsimp only [marginal]
  ring

theorem partialLeft_product {a z : Type} [Fintype a] [Fintype z]
    [DecidableEq a] [DecidableEq z] (U : Mat a) (V : Mat z) (hU : IsUnitary U)
    (ρ : Mat (a × z)) : partialLeft (evolve (U ⊗ₖ V) ρ)=evolve V (partialLeft ρ) := by
  rw [partialLeft_swap,← evolve_submatrix_equiv,kron_swap,
    FactoryMarginals.partialRight_evolve_product V U hU]
  rfl

theorem bit_energy (x : ℝ) (ρ : Mat (Fin 2)) :
    energy (work x) ρ=x*(ρ 1 1).re := by
  simp [work,energy,diagonal_mul,Matrix.trace,Fin.sum_univ_two]

theorem flip_change (x : ℝ) (ρ : Mat (Fin 2)) :
    energy (work x) (evolve ((Fin.revPerm (n:=2)).permMatrix ℂ) ρ)-energy (work x) ρ =
      x*(ρ.trace.re-2*(ρ 1 1).re) := by
  rw [bit_energy,bit_energy,Recorder.permutation_evolve]
  change x*(ρ 0 0).re-x*(ρ 1 1).re = _
  simp only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,Complex.add_re]
  ring

theorem last_success {a : Type} [Fintype a] [DecidableEq a] (ρ : Mat (a × Fin 2)) :
    FactoryFlagEffects.success (fun z => z.2) ρ=(partialLeft ρ 1 1).re := by
  rw [FactoryFlagEffects.success_sum]
  simp [Fintype.sum_prod_type,Fin.sum_univ_two,partialLeft,Complex.re_sum]

/-- A pump's additive energy ledger needs only its actual work marginal.
It is valid for arbitrary correlations between work, code and batch. -/
theorem local_change {a z : Type} [Fintype a] [Fintype z]
    [DecidableEq a] [DecidableEq z] (H : Mat a) (ρ : Mat ((a × (z × a)) × Fin 2))
    (ht : ρ.trace=1) (hz : (partialLeft ρ 1 1).re=0) (Eg Ecode : ℝ) :
    energy (FactorySwapEnergy.hamiltonian H (Eg-Ecode))
      (evolve (((FactoryReset.swap (a:=a) (b:=z)).permMatrix ℂ) ⊗ₖ
        ((Fin.revPerm (n:=2)).permMatrix ℂ)) ρ) -
      energy (FactorySwapEnergy.hamiltonian H (Eg-Ecode)) ρ =
      (energy H (partialRight (partialRight ρ))-Ecode) +
        (Eg-energy H (partialRight ((partialRight ρ).submatrix
          FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm))) := by
  have hf := flip_change (Eg-Ecode) (partialLeft ρ)
  rw [partialLeft_trace,ht,Complex.one_re,hz] at hf
  simp only [FactorySwapEnergy.hamiltonian,energy_add,energy_kron_one,energy_one_kron]
  rw [FactoryMarginals.partialRight_evolve_product _ _ (Recorder.permutation_unitary _),
    partialLeft_product _ _ FactoryReset.unitary,
    FactorySwapEnergy.batch_energy,FactorySwapEnergy.batch_energy,FactoryMarginals.swapped_batch]
  change _ + energy (work (Eg-Ecode)) _ - (_ + energy (work (Eg-Ecode)) _) = _
  linarith

end ScheduleLaw.Blueprint.FactoryPumpEnergy
