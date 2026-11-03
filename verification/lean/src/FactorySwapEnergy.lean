import FactoryMarginals
import FactoryLedger
import FactoryBattery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactorySwapEnergy
open History

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def batchHamiltonian (H : Mat a) : Mat (a × (b × a)) :=
  (1 : Mat a) ⊗ₖ ((1 : Mat b) ⊗ₖ H)

def hamiltonian (H : Mat a) (x : ℝ) : Mat ((a × (b × a)) × Fin 2) :=
  batchHamiltonian H ⊗ₖ (1 : Mat (Fin 2)) +
    (1 : Mat (a × (b × a))) ⊗ₖ diagonal ![0,(x : ℂ)]

theorem batch_energy (H : Mat a) (ρ : Mat (a × (b × a))) :
    energy (batchHamiltonian H) ρ = energy H
      (partialRight (ρ.submatrix FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm)) := by
  let e := FactoryMarginals.lastFrame (a:=a) (b:=b)
  have he : batchHamiltonian H=(H ⊗ₖ (1 : Mat (a × b))).submatrix e e := by
    ext ⟨i,r,k⟩ ⟨j,s,h⟩
    simp only [batchHamiltonian,submatrix_apply,e,FactoryMarginals.lastFrame,
      Equiv.coe_fn_mk,kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq]
    by_cases hi : i=j <;> by_cases hr : r=s <;> simp [hi,hr]
  have hρ : (ρ.submatrix e.symm e.symm).submatrix e e=ρ := by
    ext i j
    simp only [submatrix_apply,Equiv.symm_apply_apply]
  rw [he,← hρ,energy_reindex,energy_kron_one]
  rfl

theorem flip_level : evolve ((Fin.revPerm (n:=2)).permMatrix ℂ) (SupportRun.level 0)=
    SupportRun.level 1 := by
  rw [Recorder.permutation_evolve,SupportRun.level_diagonal,SupportRun.level_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal,Fin.rev]

theorem work_energy (x : ℝ) (j : Fin 2) :
    energy (diagonal ![0,(x : ℂ)]) (SupportRun.level j) = if j=0 then 0 else x := by
  rw [SupportRun.level_diagonal]
  fin_cases j <;> simp [energy,diagonal_mul_diagonal,trace_diagonal]

/-- Exact local energy ledger of the physical swap and deterministic third
work flip. Both the pre-swap physical and emitted coding marginals are actual. -/
theorem swap_pump_change (H : Mat a) (ρ : Density (a × (b × a))) (x : ℝ) :
    energy (hamiltonian H x)
      (evolve (((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ⊗ₖ
        ((Fin.revPerm (n:=2)).permMatrix ℂ)) (ρ.matrix ⊗ₖ SupportRun.level 0)) -
      energy (hamiltonian H x) (ρ.matrix ⊗ₖ SupportRun.level 0) =
      energy H (partialRight ρ.matrix) -
        energy H (partialRight (ρ.matrix.submatrix
          FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm)) + x := by
  have hev : evolve (((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ⊗ₖ
        ((Fin.revPerm (n:=2)).permMatrix ℂ)) (ρ.matrix ⊗ₖ SupportRun.level 0) =
      evolve ((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ρ.matrix ⊗ₖ SupportRun.level 1 := by
    simp only [evolve,conjTranspose_kronecker,← mul_kronecker_mul]
    rw [show ((Fin.revPerm (n:=2)).permMatrix ℂ)*SupportRun.level 0*
      ((Fin.revPerm (n:=2)).permMatrix ℂ)ᴴ=SupportRun.level 1 from flip_level]
  have ht : (evolve ((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ρ.matrix).trace=1 :=
    evolve_trace_one _ _ FactoryReset.unitary ρ.normalized
  rw [hev,hamiltonian,energy_add,energy_add,energy_kron_one,energy_kron_one,
    energy_one_kron,energy_one_kron,partialRight_kron,partialRight_kron,
    partialLeft_kron,partialLeft_kron,SupportRun.level_trace,SupportRun.level_trace,
    ht,ρ.normalized,one_smul,one_smul,one_smul,one_smul,
    work_energy,work_energy,batch_energy,batch_energy,FactoryMarginals.swapped_batch]
  norm_num
  ring

/-- Failure of flat formation changes the emitted energy as well as the
source-preparation energy. Both terms are retained in the defect. -/
theorem calibrated_defect (H : Mat a) (ρ : Density (a × (b × a))) (Eg Ecode : ℝ) :
    energy (hamiltonian H (Eg-Ecode))
      (evolve (((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) ⊗ₖ
        ((Fin.revPerm (n:=2)).permMatrix ℂ)) (ρ.matrix ⊗ₖ SupportRun.level 0)) -
      energy (hamiltonian H (Eg-Ecode)) (ρ.matrix ⊗ₖ SupportRun.level 0) =
      (energy H (partialRight ρ.matrix)-Ecode) +
        (Eg-energy H (partialRight (ρ.matrix.submatrix
          FactoryMarginals.lastFrame.symm FactoryMarginals.lastFrame.symm))) := by
  rw [swap_pump_change]
  ring

end ScheduleLaw.Blueprint.FactorySwapEnergy
