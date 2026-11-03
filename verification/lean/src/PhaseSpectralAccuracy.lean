import PhaseSpectralLabels
import PhasePacketMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhaseSpectralAccuracy
open PhaseVectorDistance PhaseReferenceBound PhasePacketMap PhaseGateDilation
variable {s ι : Type} [Fintype s] [DecidableEq s] [Fintype ι] [DecidableEq ι]

private abbrev mmul {m n k : Type} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n k ℂ) : Matrix m k ℂ :=
  @HMul.hMul (Matrix m n ℂ) (Matrix n k ℂ) (Matrix m k ℂ) inferInstance A B


theorem error_factor (H : Hamiltonian s) (U : Mat s)
    (l : s → PhaseLatticeBox.Lattice ι) (L : ℕ) :
    (evolve (basis H ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))
      (FinitePhaseShell.gate l (PhaseLatticeBox.box ι L) (inBasis H U)))*
        embed (PhasePacketDensity.packet L)-embed (PhasePacketDensity.packet L)*U=
    (basis H ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))*
      PhaseGateAccuracy.errorMatrix l L (inBasis H U)*(basis H)ᴴ := by
  let J := embed (PhasePacketDensity.packet (ι:=ι) L) (a:=s)
  let W := basis H
  let V := FinitePhaseShell.gate l (PhaseLatticeBox.box ι L) (inBasis H U)
  have hJ : (Wᴴ ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))*J=J*Wᴴ := intertwine _ _
  have hJ' : (W ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))*J=J*W := intertwine _ _
  have hU : W*(inBasis H U)*Wᴴ=U := by
    dsimp only [inBasis,evolve]
    rw [conjTranspose_conjTranspose]
    change W*(Wᴴ*U*W)*Wᴴ=U
    simp only [← Matrix.mul_assoc]
    rw [(basis_unitary H).2,one_mul,Matrix.mul_assoc U,(basis_unitary H).2,mul_one]
  rw [← shell_error l L (inBasis H U)]
  change (W ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))*V*
    (W ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))ᴴ*J-J*U=
      (W ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))*(V*J-J*inBasis H U)*Wᴴ
  rw [conjTranspose_kronecker,conjTranspose_one,Matrix.mul_assoc _ _ J,hJ]
  rw [Matrix.mul_sub,Matrix.sub_mul]
  congr 1
  · simp only [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc _ J,hJ']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W,hU]

theorem error_bound (H : Hamiltonian s) (U : Mat s) (hU : IsUnitary U)
    (l : s → PhaseLatticeBox.Lattice ι) (hl : ∀ j k,0≤l j k ∧ l j k≤1)
    (L : ℕ) (hL : 0<L) (hs : 0<Fintype.card s) :
    ‖((evolve (basis H ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L)))
      (FinitePhaseShell.gate l (PhaseLatticeBox.box ι L) (inBasis H U)))*
        embed (PhasePacketDensity.packet L)-embed (PhasePacketDensity.packet L)*U :
        Matrix (s × ↥(PhaseLatticeBox.box ι L)) s ℂ)‖≤
      ((Fintype.card s : ℝ)*(((Fintype.card ι : ℝ)+1)*Real.pi/(L+1 : ℝ)))*‖(basis H)ᴴ‖ := by
  have he := congrArg (fun M : Matrix (s × ↥(PhaseLatticeBox.box ι L)) s ℂ => ‖M‖) (error_factor H U l L)
  apply he.le.trans
  rw [Matrix.mul_assoc]
  have h1 : IsUnitary (1 : Mat ↥(PhaseLatticeBox.box ι L)) := by constructor <;> simp
  let W := basis H ⊗ₖ (1 : Mat ↥(PhaseLatticeBox.box ι L))
  let M : Matrix (s × ↥(PhaseLatticeBox.box ι L)) s ℂ :=
    PhaseGateAccuracy.errorMatrix l L (inBasis H U)*(basis H)ᴴ
  have hW : IsUnitary W := unitary_kron (basis_unitary H) h1
  change ‖(mmul W M : Matrix (s × ↥(PhaseLatticeBox.box ι L)) s ℂ)‖≤_
  have hn : ‖(mmul W M : Matrix (s × ↥(PhaseLatticeBox.box ι L)) s ℂ)‖=‖M‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [column_square (mmul W M),column_square M]
    apply Finset.sum_congr rfl
    intro j _
    change ‖vector (W *ᵥ (fun i => M i j))‖^2=‖vector (fun i => M i j)‖^2
    rw [norm_unitary W hW]
  rw [hn]
  change ‖(PhaseGateAccuracy.errorMatrix l L (inBasis H U)*(basis H)ᴴ :
    Matrix (s × ↥(PhaseLatticeBox.box ι L)) s ℂ)‖≤_
  apply (Matrix.frobenius_norm_mul _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply column_bound _ _ (by positivity) hs
  intro j
  exact PhaseGateAccuracy.column_error l hl L hL _
    (conjugate_unitary _ _ hU (adjoint_unitary _ (basis_unitary H))) j

end ScheduleLaw.Blueprint.PhaseSpectralAccuracy
