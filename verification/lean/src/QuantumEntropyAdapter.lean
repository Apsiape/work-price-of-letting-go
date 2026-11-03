import GibbsAccounting
import QuantumInfo.Entropy.SSA
import QuantumInfo.Entropy.Relative

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder InnerProductSpace RealInnerProductSpace
namespace ScheduleLaw

def Density.toMState {a : Type} [Fintype a] [DecidableEq a] (ρ : Density a) : MState a where
  M := ⟨ρ.matrix,ρ.positive.isHermitian⟩
  nonneg := HermitianMat.zero_le_iff.mpr ρ.positive
  tr := by simpa [HermitianMat.trace,ρ.normalized]

theorem density_entropy_eq_library {a : Type} [Fintype a] [DecidableEq a] (ρ : Density a) :
    entropy ρ.matrix = Sᵥₙ ρ.toMState := by
  rw [entropy_of_hermitian _ ρ.positive.isHermitian]
  rfl

def Density.right {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Density (a × b)) : Density a :=
  ⟨partialRight ρ.matrix,partialRight_positive ρ.positive,
    (partialRight_trace _).trans ρ.normalized⟩

def Density.left {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Density (a × b)) : Density b :=
  ⟨partialLeft ρ.matrix,partialLeft_positive ρ.positive,
    (partialLeft_trace _).trans ρ.normalized⟩

theorem toMState_right {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Density (a × b)) : ρ.right.toMState = ρ.toMState.traceRight := by
  apply MState.ext_m
  rfl

theorem toMState_left {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Density (a × b)) : ρ.left.toMState = ρ.toMState.traceLeft := by
  apply MState.ext_m
  rfl

theorem entropy_subadditive {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ρ : Density (a × b)) :
    entropy ρ.matrix ≤ entropy (partialRight ρ.matrix) + entropy (partialLeft ρ.matrix) := by
  have h := Sᵥₙ_subadditivity ρ.toMState
  rw [← toMState_right,← toMState_left,← density_entropy_eq_library,
    ← density_entropy_eq_library,← density_entropy_eq_library] at h
  exact h

theorem entropy_submatrix_equiv {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (ρ : Mat b) (hρ : ρ.IsHermitian) :
    entropy (ρ.submatrix e e) = entropy ρ := by
  rw [entropy_eq_charpoly_roots _ (hρ.submatrix e),entropy_eq_charpoly_roots _ hρ]
  change (((ρ.reindex e.symm e.symm).charpoly.roots).map _).sum = _
  rw [charpoly_reindex]

theorem correlation_nonnegative_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) :
    0 ≤ (engineLedger e t).totalCorrelation := by
  have hf := bodyOutput_density e.extension t
  let ρ : Density (Fin e.c × (Fin e.w × Fin e.r)) :=
    ⟨(bodyOutput e.extension t).submatrix e.split.symm e.split.symm,
      hf.1.submatrix e.split.symm,(submatrix_trace_equiv _ _).trans hf.2⟩
  have h1 := entropy_subadditive ρ
  have h2 := entropy_subadditive ρ.left
  have he := entropy_submatrix_equiv e.split.symm (bodyOutput e.extension t) hf.1.isHermitian
  change entropy ρ.matrix = entropy (bodyOutput e.extension t) at he
  dsimp [Density.left,Density.right,ρ] at h1 h2
  unfold engineLedger controllerFinal batteryFinal reservoirFinal batteryReservoirFinal
  linarith

theorem library_log_matrix {a : Type} [Fintype a] [DecidableEq a] (ρ : Density a) :
    ρ.toMState.M.log.mat = matrixLog ρ.matrix := by
  rw [matrixLog,dif_pos ρ.positive.isHermitian,← ρ.positive.isHermitian.cfc_eq]
  rfl

theorem relative_entropy_nonnegative {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Density a) (hσ : σ.matrix.PosDef) :
    0 ≤ faithfulRelativeEntropy ρ.matrix σ.matrix := by
  letI : HermitianMat.NonSingular σ.toMState.M := HermitianMat.nonSingular_of_posDef hσ
  have hk : σ.toMState.M.ker ≤ ρ.toMState.M.ker := by
    rw [HermitianMat.nonSingular_ker_bot]
    exact bot_le
  have h := inner_log_sub_log_nonneg (ρ := ρ.toMState) (σ := σ.toMState) hk
  have he : ⟪ρ.toMState.M,ρ.toMState.M.log - σ.toMState.M.log⟫_ℝ =
      faithfulRelativeEntropy ρ.matrix σ.matrix := by
    rw [HermitianMat.inner_eq_re_trace,HermitianMat.mat_sub,library_log_matrix,library_log_matrix]
    change (ρ.matrix * (matrixLog ρ.matrix - matrixLog σ.matrix)).trace.re = _
    rw [faithfulRelativeEntropy,entropy_trace_log _ ρ.positive.isHermitian]
    simp [mul_sub,trace_sub]
  rwa [he] at h

end ScheduleLaw
