import FactoryFormation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCapital
open History

theorem zero_gibbs (β : ℝ) (c : ℕ) (hc : 0<c) :
    gibbs β (FiniteFlat.zeroHamiltonian c)=(FactoryFormation.flat c hc).matrix := by
  have hH : FiniteFlat.zeroHamiltonian c=
      FlatMatrix.diagonalHamiltonian (Fin c) (fun _ => 0) := by
    simp [FiniteFlat.zeroHamiltonian,FlatMatrix.diagonalHamiltonian]
  rw [hH,FlatMatrix.diagonal_gibbs]
  ext i j
  simp [FactoryFormation.flat,FactoryCoding.flatDensity,Matrix.diagonal,Matrix.one_apply,
    Complex.ofReal_inv]

theorem relative_self {a : Type} [Fintype a] [DecidableEq a] (ρ : Density a) :
    faithfulRelativeEntropy ρ.matrix ρ.matrix=0 := by
  rw [faithfulRelativeEntropy,entropy_trace_log _ ρ.positive.isHermitian]
  ring

/-- Flat zero-Hamiltonian coding workspace is Gibbs stock and has zero
startup relative free energy. This is the capital actually used by Formation. -/
theorem flat_charge (β : ℝ) (c : ℕ) (hc : 0<c) :
    faithfulRelativeEntropy (FactoryFormation.flat c hc).matrix
      (gibbs β (FiniteFlat.zeroHamiltonian c))/β=0 := by
  rw [zero_gibbs β c hc,relative_self,zero_div]

theorem formation_charged {d : ℕ} (hd : 0<d) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef) (m c w aux : ℕ)
    (hm : 0 < m) (hc : 0 < c) (hw : 0 < w) (haux : 0 < aux)
    (HA : Hamiltonian (Fin aux)) (E : Fin w → ℝ) (initial nominal : Fin w)
    (U : Mat (Fin c × (Fin w × Fin ((Fintype.card (Fin m → Fin d))*aux))))
    (hU : IsUnitary U) :
    Driven.CapitalCharged
      (FactoryFormation.formation hd β hβ τ q hq m c w aux hm hc hw haux HA E
        initial nominal U hU).hardware := by
  change faithfulRelativeEntropy (FactoryFormation.flat c hc).matrix
    (gibbs β (FiniteFlat.zeroHamiltonian c))/β≤0
  rw [flat_charge]

end ScheduleLaw.Blueprint.FactoryCapital
