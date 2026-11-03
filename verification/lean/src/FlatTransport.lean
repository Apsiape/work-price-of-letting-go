import FlatOutput
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FiniteFlat

theorem adjoint_unitary {a : Type} [Fintype a] [DecidableEq a]
    {V : Mat a} (hV : IsUnitary V) : IsUnitary Vᴴ := by
  constructor
  · simpa only [conjTranspose_conjTranspose] using hV.2
  · simpa only [conjTranspose_conjTranspose] using hV.1

theorem conserving_mul {a : Type} [Fintype a] {U V H : Mat a}
    (hU : Conserves U H) (hV : Conserves V H) : Conserves (U*V) H := by
  unfold Conserves at *
  calc
    (U*V)ᴴ*H*(U*V) = Vᴴ*(Uᴴ*H*U)*V := by simp only [conjTranspose_mul,mul_assoc]
    _ = H := by rw [hU,hV]

theorem system_basis_conserves {d r : ℕ} (HR : Hamiltonian (Fin r)) (x : ℝ)
    (V : Mat (Fin d)) (hV : IsUnitary V) :
    Conserves (V ⊗ₖ (1 : Mat (Fin 2 × Fin r)))
      (converterHamiltonian (zeroHamiltonian d) HR x) := by
  unfold Conserves converterHamiltonian zeroHamiltonian
  simp only [zero_kronecker,zero_add,conjTranspose_kronecker,conjTranspose_one,
    ← mul_kronecker_mul,mul_one,one_mul]
  rw [hV.1]

def rotatedConverter {d : ℕ} {β x : ℝ}
    (C : SupportConverter β (zeroHamiltonian d) x) (V : Mat (Fin d))
    (hV : IsUnitary V) : SupportConverter β (zeroHamiltonian d) x where
  r := C.r
  r_pos := C.r_pos
  HR := C.HR
  U := (V ⊗ₖ (1 : Mat (Fin 2 × Fin C.r))) * C.U *
    (V ⊗ₖ (1 : Mat (Fin 2 × Fin C.r)))ᴴ
  unitary := by
    have hone : IsUnitary (1 : Mat (Fin 2 × Fin C.r)) := by constructor <;> simp
    have hW := unitary_kron hV hone
    exact unitary_mul (unitary_mul hW C.unitary) (adjoint_unitary hW)
  conserves := by
    have hW := system_basis_conserves C.HR x V hV
    have hWs := system_basis_conserves C.HR x Vᴴ (adjoint_unitary hV)
    simp only [conjTranspose_kronecker,conjTranspose_one] at ⊢
    exact conserving_mul (conserving_mul hW C.conserves) hWs

theorem flat_initial_invariant {d : ℕ} {b : Type} [Fintype b] [DecidableEq b]
    (V : Mat (Fin d)) (hV : IsUnitary V) (A : Mat b) :
    evolve (V ⊗ₖ (1 : Mat b))ᴴ ((((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ A) =
      (((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ A := by
  simp only [evolve,conjTranspose_kronecker,conjTranspose_one,
    conjTranspose_conjTranspose,← mul_kronecker_mul,mul_one,one_mul,
    Matrix.mul_smul,Matrix.smul_mul,hV.1]

theorem system_mask_covariant {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (V : Mat a) (M : Mat b) (A : Mat (a × b)) :
    ((1 : Mat a) ⊗ₖ M) * evolve (V ⊗ₖ (1 : Mat b)) A =
      evolve (V ⊗ₖ (1 : Mat b)) (((1 : Mat a) ⊗ₖ M) * A) := by
  have hc : ((1 : Mat a) ⊗ₖ M) * (V ⊗ₖ (1 : Mat b)) =
      (V ⊗ₖ (1 : Mat b)) * ((1 : Mat a) ⊗ₖ M) := by
    simp only [← mul_kronecker_mul,one_mul,mul_one]
  simp only [evolve]
  rw [← mul_assoc,← mul_assoc,hc]
  simp only [mul_assoc]

theorem rotated_output {d : ℕ} {β x : ℝ}
    (C : SupportConverter β (zeroHamiltonian d) x) (V : Mat (Fin d)) (hV : IsUnitary V) :
    flatOutput (rotatedConverter C V hV) = evolve V (flatOutput C) := by
  let N : Mat (Fin d × (Fin 2 × Fin C.r)) :=
    (((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ
      (pureMatrix (fun j : Fin 2 => if j=0 then 1 else 0) ⊗ₖ gibbs β C.HR)
  let M : Mat (Fin d × (Fin 2 × Fin C.r)) :=
    (1 : Mat (Fin d)) ⊗ₖ
      (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ (1 : Mat (Fin C.r)))
  let W : Mat (Fin d × (Fin 2 × Fin C.r)) := V ⊗ₖ (1 : Mat (Fin 2 × Fin C.r))
  rw [FlatOutput.flatOutput_eq]
  change partialRight (M * evolve (W*C.U*Wᴴ) N) = _
  rw [evolve_mul,evolve_mul,flat_initial_invariant V hV]
  change partialRight (M * evolve W (evolve C.U N)) = _
  rw [system_mask_covariant,partialRight_evolve_kron_one]
  rw [FlatOutput.flatOutput_eq C]

end ScheduleLaw.Blueprint.FiniteFlat
