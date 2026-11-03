import SupportCoordinates
import ThermalContactEnergy
import FlagReference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryGibbs
open History

theorem cfc_in_basis {a : Type} [Fintype a] [DecidableEq a]
    (H : Hamiltonian a) (U : Mat a) (hU : IsUnitary U) (E : a → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ))))
    (f : ℝ → ℝ) (hf : Continuous f) :
    H.hermitian.cfc f = evolve U (diagonal (fun i => (f (E i) : ℂ))) := by
  letI := matrixCStarStructure a
  let φ := Unitary.conjStarAlgAut ℂ (Mat a) (⟨U,hU⟩ : unitaryGroup a ℂ)
  let D : Mat a := diagonal (fun i => (E i : ℂ))
  have hφ : φ D=H.matrix := hH.symm
  have hd : cfc f D=diagonal (fun i => (f (E i) : ℂ)) := by
    exact ((FlatMatrix.diagonalHamiltonian a E).hermitian.cfc_eq f).trans
      (FlatMatrix.diagonal_cfc a E f hf)
  have hm := StarAlgHomClass.map_cfc φ f D
    (hf := hf.continuousOn)
    (hφ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := (FlatMatrix.diagonalHamiltonian a E).hermitian)
    (hφa := by rw [hφ]; exact H.hermitian)
  rw [hφ] at hm
  rw [← H.hermitian.cfc_eq,← hm,hd]
  rfl

theorem partition_in_basis {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (H : Hamiltonian a) (U : Mat a) (hU : IsUnitary U) (E : a → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ)))) :
    partition β H=∑ i,Real.exp (-β*E i) := by
  have ht := congrArg Matrix.trace (cfc_in_basis H U hU E hH
    (fun x => Real.exp (-β*x)) (by fun_prop))
  unfold Matrix.IsHermitian.cfc at ht
  rw [trace_unitary_conjugation] at ht
  change _ = (evolve U (diagonal (fun i => (Real.exp (-β*E i) : ℂ)))).trace at ht
  rw [evolve,trace_mul_cycle,hU.1,one_mul,trace_diagonal] at ht
  simp only [trace_diagonal,Function.comp_apply,← Complex.ofReal_sum] at ht
  simpa only [partition,Complex.re_sum,Complex.ofReal_re] using congrArg Complex.re ht

theorem gibbs_in_basis {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (H : Hamiltonian a) (U : Mat a) (hU : IsUnitary U) (E : a → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun i => (E i : ℂ)))) :
    gibbs β H=evolve U (diagonal (fun i =>
      ((Real.exp (-β*E i)/(∑ j,Real.exp (-β*E j)) : ℝ) : ℂ))) := by
  change H.hermitian.cfc (fun x => Real.exp (-β*x)/partition β H)=_
  rw [partition_in_basis β H U hU E hH]
  exact cfc_in_basis H U hU E hH _ (by fun_prop)

def tangent {a : Type} [Fintype a] [DecidableEq a] (β : ℝ) (q : Density a) : Hamiltonian a :=
  ⟨tangentHamiltonian β q,tangentHamiltonian_hermitian β q⟩

theorem tangent_gibbs {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (hβ : β≠0) (q : Density a) (hq : q.matrix.PosDef) :
    gibbs β (tangent β q)=q.matrix := by
  let U : Mat a := q.positive.isHermitian.eigenvectorUnitary
  let lam : a → ℝ := q.positive.isHermitian.eigenvalues
  have hU : IsUnitary U := q.positive.isHermitian.eigenvectorUnitary.property
  have he : tangentHamiltonian β q=evolve U (diagonal (fun i => ((-Real.log (lam i)/β : ℝ) : ℂ))) := by
    unfold tangentHamiltonian matrixLog
    rw [dif_pos q.positive.isHermitian]
    unfold Matrix.IsHermitian.cfc
    change (((-1/β : ℝ) : ℂ) • (U*(diagonal (fun i => (Real.log (lam i) : ℂ)))*Uᴴ)) = _
    rw [← smul_mul_assoc,← Matrix.mul_smul,← diagonal_smul]
    apply congrArg (fun D : Mat a => U*D*Uᴴ)
    apply congrArg diagonal
    funext i
    change ((-1/β : ℝ) : ℂ)*(Real.log (lam i) : ℂ) = ((-Real.log (lam i)/β : ℝ) : ℂ)
    rw [← Complex.ofReal_mul]
    congr 1
    ring
  have hlam (i : a) : 0<lam i := hq.eigenvalues_pos i
  have hexp (i : a) : Real.exp (-β*(-Real.log (lam i)/β))=lam i := by
    rw [show -β*(-Real.log (lam i)/β)=Real.log (lam i) by field_simp]
    exact Real.exp_log (hlam i)
  have hsum : ∑ i,lam i=1 := density_eigenvalues_sum q
  rw [gibbs_in_basis β (tangent β q) U hU _ he]
  simp only [hexp,hsum,div_one]
  exact q.positive.isHermitian.spectral_theorem.symm

end ScheduleLaw.Blueprint.FactoryGibbs
