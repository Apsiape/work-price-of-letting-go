import BlueprintContracts
import W2.SineEstimates

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

def boltzmann {d : ℕ} (β : ℝ) (H : Hamiltonian (Fin d)) : Mat (Fin d) :=
  H.hermitian.cfc (fun x => Real.exp (-β*x))

def converterHamiltonian {d r : ℕ} (H : Hamiltonian (Fin d))
    (HR : Hamiltonian (Fin r)) (x : ℝ) : Mat (Fin d × (Fin 2 × Fin r)) :=
  H.matrix ⊗ₖ (1 : Mat (Fin 2 × Fin r)) + (1 : Mat (Fin d)) ⊗ₖ
    ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat (Fin r)) + (1 : Mat (Fin 2)) ⊗ₖ HR.matrix)

def converterFrame (d r z : ℕ) : ((Fin d × Fin z) × (Fin 2 × Fin r)) ≃
    (Fin d × (Fin 2 × Fin r)) × Fin z where
  toFun a := ((a.1.1,a.2),a.1.2)
  invFun a := ((a.1.1,a.2),a.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

structure SupportConverter {d : ℕ} (β : ℝ) (H : Hamiltonian (Fin d)) (x : ℝ) where
  r : ℕ
  r_pos : 0 < r
  HR : Hamiltonian (Fin r)
  U : Mat (Fin d × (Fin 2 × Fin r))
  unitary : IsUnitary U
  conserves : Conserves U (converterHamiltonian H HR x)

namespace SupportConverter

def run {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (z : ℕ) (ρ : Mat (Fin d × Fin z)) :
    Mat ((Fin d × (Fin 2 × Fin C.r)) × Fin z) :=
  evolve (C.U ⊗ₖ (1 : Mat (Fin z)))
    ((ρ ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=0 then 1 else 0) ⊗ₖ gibbs β C.HR)).submatrix
      (converterFrame d C.r z).symm (converterFrame d C.r z).symm)

end SupportConverter

end ScheduleLaw.Blueprint
