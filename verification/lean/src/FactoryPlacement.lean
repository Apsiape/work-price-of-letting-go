import FactoryCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPlacement
open History

variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

def place (e : a ≃ b × c) (U : Mat b) : Mat a :=
  (U ⊗ₖ (1 : Mat c)).submatrix e e

theorem unitary (e : a ≃ b × c) (U : Mat b) (hU : IsUnitary U) : IsUnitary (place e U) :=
  unitary_submatrix e (unitary_kron hU (by constructor <;> simp))

omit [DecidableEq a] [DecidableEq b] in
theorem mul (e : a ≃ b × c) (U V : Mat b) : place e (U*V)=place e U*place e V := by
  simp only [place,submatrix_mul_equiv,← mul_kronecker_mul,one_mul]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] in
theorem star (e : a ≃ b × c) (U : Mat b) : (place e U)ᴴ=place e Uᴴ := by
  simp only [place,conjTranspose_submatrix,conjTranspose_kronecker,conjTranspose_one]

theorem whole_evolution (e : a ≃ b × c) (U : Mat b) (ρ : Mat a) :
    (evolve (place e U) ρ).submatrix e.symm e.symm =
      evolve (U ⊗ₖ (1 : Mat c)) (ρ.submatrix e.symm e.symm) := by
  rw [← evolve_submatrix_equiv]
  congr 1
  ext i j
  simp only [place,submatrix_apply,Equiv.apply_symm_apply]

theorem operated_marginal (e : a ≃ b × c) (U : Mat b) (ρ : Mat a) :
    partialRight ((evolve (place e U) ρ).submatrix e.symm e.symm) =
      evolve U (partialRight (ρ.submatrix e.symm e.symm)) := by
  rw [whole_evolution,partialRight_evolve_kron_one]

theorem rest_invariant (e : a ≃ b × c) (U : Mat b) (hU : IsUnitary U) (ρ : Mat a) :
    partialLeft ((evolve (place e U) ρ).submatrix e.symm e.symm) =
      partialLeft (ρ.submatrix e.symm e.symm) := by
  rw [whole_evolution,partialLeft_swap,← evolve_submatrix_equiv,kron_swap,
    partialRight_evolve_one_kron U _ hU]
  rfl

theorem conserves (e : a ≃ b × c) (U H : Mat b) (K : Mat c)
    (hU : IsUnitary U) (hcon : Conserves U H) :
    Conserves (place e U) ((H ⊗ₖ (1 : Mat c)+(1 : Mat b) ⊗ₖ K).submatrix e e) := by
  apply conserves_reindex e
  unfold Conserves at *
  simp only [conjTranspose_kronecker,conjTranspose_one,mul_add,add_mul,
    ← mul_kronecker_mul,mul_one,one_mul,hcon,hU.1]

end ScheduleLaw.Blueprint.FactoryPlacement
