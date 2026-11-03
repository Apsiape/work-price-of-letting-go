import PhaseGateAccuracy
import PhaseTensorVectors

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhasePacketMap
open PhaseVectorDistance PhaseReferenceBound
variable {a p r : Type} [Fintype a] [Fintype p] [Fintype r] [DecidableEq a] [DecidableEq p]

def embed (v : p → ℂ) : Matrix (a × p) a ℂ := fun x j =>
  (if x.1=j then 1 else 0)*v x.2

theorem intertwine (W : Mat a) (v : p → ℂ) :
    (W ⊗ₖ (1 : Mat p))*embed v=embed v*W := by
  ext ⟨i,x⟩ j
  change (∑ k : a × p, W i k.1 * (1 : Mat p) x k.2 * embed v k j)=
    ∑ k : a, embed v (i,x) k * W k j
  simp [Matrix.mul_apply,embed,kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
    ite_mul,mul_ite,mul_assoc,mul_comm,mul_left_comm]

theorem column_square (M : Matrix a r ℂ) : ‖M‖^2=∑ j,‖vector (fun i => M i j)‖^2 := by
  rw [← vector_matrix_norm,EuclideanSpace.norm_sq_eq]
  simp only [vector,PiLp.toLp_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (EuclideanSpace.norm_sq_eq (vector (fun i => M i j))).symm

theorem unitary_left (W : Mat a) (hW : IsUnitary W) (M : Matrix a r ℂ) : ‖W*M‖=‖M‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [column_square,column_square]
  apply Finset.sum_congr rfl
  intro j _
  change ‖vector (W *ᵥ (fun i => M i j))‖^2=‖vector (fun i => M i j)‖^2
  rw [norm_unitary W hW]

variable {s ι : Type} [Fintype s] [DecidableEq s] [Fintype ι] [DecidableEq ι]

theorem shell_error (l : s → PhaseLatticeBox.Lattice ι) (L : ℕ) (U : Mat s) :
    FinitePhaseShell.gate l (PhaseLatticeBox.box ι L) U*embed (PhasePacketDensity.packet L)-
      embed (PhasePacketDensity.packet L)*U=PhaseGateAccuracy.errorMatrix l L U := by
  ext x j
  change (∑ k, FinitePhaseShell.gate l (PhaseLatticeBox.box ι L) U x k * embed (PhasePacketDensity.packet L) k j)-
    (∑ k, embed (PhasePacketDensity.packet L) x k * U k j)=_
  simp only [Matrix.sub_apply,Matrix.mul_apply,embed,Fintype.sum_prod_type,
    PhaseGateAccuracy.errorMatrix,PhaseGateAccuracy.errorColumn,PhaseGateColumn.column]
  simp [ite_mul,mul_ite,mul_assoc,mul_comm,mul_left_comm]

end ScheduleLaw.Blueprint.PhasePacketMap
