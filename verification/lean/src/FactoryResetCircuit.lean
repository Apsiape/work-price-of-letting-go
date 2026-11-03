import FactoryReset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryResetCircuit
open History

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def circuit (U : Mat (a × b)) : Mat (a × (b × a)) :=
  (FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ *
    (U ⊗ₖ (1 : Mat a)).submatrix (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm

theorem unitary (U : Mat (a × b)) (hU : IsUnitary U) : IsUnitary (circuit U) :=
  unitary_mul FactoryReset.unitary (unitary_submatrix _ (unitary_kron hU (by constructor <;> simp)))

/-- Arbitrary preprocessing retains all correlations. A single final Gibbs
 swap then restores the complete controller as a product with every old
 controller register, work register, retired bath and coherent reference. -/
theorem whole_rest_return (U : Mat (a × b)) (ρ : Mat (a × b)) (σ : Mat a) :
    evolve (circuit U) ((ρ ⊗ₖ σ).submatrix
      (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm) =
      σ ⊗ₖ ((evolve U ρ).submatrix (Equiv.prodComm b a) (Equiv.prodComm b a)) := by
  unfold circuit
  rw [evolve_mul,evolve_submatrix_equiv]
  have he : evolve (U ⊗ₖ (1 : Mat a)) (ρ ⊗ₖ σ) = evolve U ρ ⊗ₖ σ := by
    simp only [evolve,conjTranspose_kronecker,conjTranspose_one,← mul_kronecker_mul,
      one_mul,mul_one]
  rw [he,FactoryReset.whole_rest_return]

end ScheduleLaw.Blueprint.FactoryResetCircuit
