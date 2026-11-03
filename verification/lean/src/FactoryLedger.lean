import FactoryRate
import FactoryGibbsProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryLedger
open History FactoryGibbs FactoryTensor FiniteResidue

/-- The literal tangent Hamiltonian has partition one; this fixes the additive
energy constant needed by the factory debit ledger. -/
theorem tangent_partition {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (hβ : β≠0) (q : Density a) (hq : q.matrix.PosDef) :
    partition β (tangent β q)=1 := by
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
  rw [partition_in_basis β (tangent β q) U hU _ he]
  simpa only [hexp] using hsum

/-- Signed credits of preparation, flat formation, the swap/pump, and
extraction. Their negative sum is the literal four-register nominal debit. -/
theorem signed_debit (β D R K Z Eg Ecode : ℝ) (hD : 0<D) (hR : 0<R) (hK : 0<K) :
    -((-Eg-Real.log Z/β-1) + (-Real.log (D*R/K)/β) +
      (Eg-Ecode) + (Real.log D/β-1)) =
      Ecode+(Real.log R-Real.log K)/β+Real.log Z/β+2 := by
  rw [Real.log_div (mul_pos hD hR).ne' hK.ne',Real.log_mul hD.ne' hR.ne']
  ring

theorem signed_debit_partition_one (β D R K Eg Ecode : ℝ)
    (hD : 0<D) (hR : 0<R) (hK : 0<K) :
    -((-Eg-Real.log 1/β-1) + (-Real.log (D*R/K)/β) +
      (Eg-Ecode) + (Real.log D/β-1)) =
      Ecode+(Real.log R-Real.log K)/β+2 := by
  simpa only [Real.log_one,zero_div,add_zero] using
    signed_debit β D R K 1 Eg Ecode hD hR hK

end ScheduleLaw.Blueprint.FactoryLedger
