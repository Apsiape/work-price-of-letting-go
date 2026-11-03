import ThermalBodyContact

/-! Exact energy identities for a thermal two-sector body contact. These
apply to the actual finite circuit constructed in ThermalBodyContact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

theorem energy_pullback {a : Type} [Fintype a] (H U ρ : Mat a) :
    energy H (evolve U ρ) = energy (Uᴴ*H*U) ρ := by
  unfold energy evolve
  rw [← mul_assoc,trace_mul_cycle H (U*ρ) Uᴴ]
  simp only [mul_assoc]

theorem energy_diagonal_blocks {a b : Type} [Fintype a] [Fintype b]
    (H : Mat a) (K : Mat b) (X : Matrix a b ℂ) (Y : Matrix b a ℂ) (A : Mat a) (B : Mat b) :
    energy (fromBlocks H X Y K) (ClassicalFlag.block A B) = energy H A + energy K B := by
  simp [energy,ClassicalFlag.block,fromBlocks_multiply,trace,Fintype.sum_sum_type]

theorem rotatedFlag_body_energy {d : ℕ} (Q C F ρ : Mat (Fin d))
    (hC : C.IsHermitian) (hF : F.IsHermitian) (p : ℝ) :
    energy (ClassicalFlag.block Q Q)
      (evolve (fromBlocks C (-F) F C)
        (ClassicalFlag.block (((1-p : ℝ) : ℂ) • ρ) ((p : ℂ) • ρ))) =
      energy (C*Q*C+F*Q*F) ρ := by
  rw [energy_pullback]
  simp only [ClassicalFlag.block,fromBlocks_conjTranspose,conjTranspose_neg,hC.eq,hF.eq,
    fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,neg_mul,mul_neg,neg_neg]
  change energy (fromBlocks _ _ _ _) (ClassicalFlag.block _ _) = _
  rw [energy_diagonal_blocks,ClassicalFlag.energy_weight,ClassicalFlag.energy_weight]
  rw [add_comm (F*Q*F) (C*Q*C)]
  ring

theorem flagReference_tangent_gap {d : ℕ} (β : ℝ) (hβ : β ≠ 0)
    (q : Density (Fin d)) (hq : q.matrix.PosDef) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (M : ℝ) (hgap : Real.log (1-p)-Real.log p = β*M) :
    tangentHamiltonian β (flagReference q hq p hp hp1) =
      (ClassicalFlag.block (tangentHamiltonian β q) (tangentHamiltonian β q) +
        fromBlocks 0 0 0 ((M : ℂ) • (1 : Mat (Fin d))) +
        (((-Real.log (1-p)/β : ℝ) : ℂ) • 1)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  have he : (-1/β)*Real.log p = (-Real.log (1-p)/β)+M := by
    field_simp [hβ]
    nlinarith
  have he0 : (((-1/β : ℝ) : ℂ)) * (Real.log (1-p) : ℂ) = ((-Real.log (1-p)/β : ℝ) : ℂ) := by
    push_cast; ring
  have he1 : (((-1/β : ℝ) : ℂ)) * (Real.log p : ℂ) =
      ((-Real.log (1-p)/β : ℝ) : ℂ)+(M : ℂ) := by exact_mod_cast he
  push_cast at he0 he1
  unfold tangentHamiltonian
  rw [flagReference_log]
  change ((((-1/β : ℝ) : ℂ) • ClassicalFlag.block
    (matrixLog q.matrix+(Real.log (1-p) : ℂ) • 1)
    (matrixLog q.matrix+(Real.log p : ℂ) • 1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  apply congrArg (fun X : Mat (Fin d ⊕ Fin d) => X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
  ext i j
  cases i <;> cases j <;>
    simp [ClassicalFlag.block,Matrix.one_apply,smul_add,smul_smul,he0,he1]
  all_goals split_ifs <;> simp_all [mul_add] <;> ring

theorem energy_identity_trace_zero {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Mat a) (hρ : ρ.trace=1) (hσ : σ.trace=1) (c : ℝ) :
    energy ((c : ℂ) • (1 : Mat a)) (ρ-σ) = 0 := by
  simp [energy,smul_mul_assoc,trace_smul,trace_sub,hρ,hσ]

theorem flag_input_trace {a : Type} [Fintype a] (ρ : Mat a) (hρ : ρ.trace=1) (p : ℝ) :
    (ClassicalFlag.block (((1-p : ℝ) : ℂ) • ρ) ((p : ℂ) • ρ)).trace = 1 := by
  rw [ClassicalFlag.block_trace,trace_smul,trace_smul,hρ]
  simp

theorem evolve_trace_one {a : Type} [Fintype a] [DecidableEq a]
    (U ρ : Mat a) (hU : IsUnitary U) (hρ : ρ.trace=1) : (evolve U ρ).trace=1 := by
  unfold evolve
  rw [trace_mul_cycle,hU.1,one_mul,hρ]

theorem tangentHamiltonian_hermitian {a : Type} [Fintype a] [DecidableEq a]
    (β : ℝ) (q : Density a) : (tangentHamiltonian β q).IsHermitian := by
  unfold tangentHamiltonian
  rw [matrixLog_eq_cfc _ q.positive.isHermitian]
  exact IsSelfAdjoint.smul
    (show IsSelfAdjoint (((-1/β : ℝ) : ℂ)) from by rw [isSelfAdjoint_iff]; simp)
    (cfc_predicate Real.log q.matrix)

theorem thermalBodyContact_linearized {I : Inventory} {S : Schedule I}
    (β : ℝ) (hβ : β ≠ 0) (e : Extension S) (q : Density (Fin e.b)) (hq : q.matrix.PosDef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (M : ℝ)
    (hgap : Real.log (1-p)-Real.log p = β*M)
    (U : Mat (Fin e.b ⊕ Fin e.b)) (hU : IsUnitary U) {r : ℕ} (t : Tester S r) :
    physicalLinearized β (thermalBodyContact e p hp hp1 U hU) (flagReference q hq p hp hp1) t =
      handoff e t + energy
        (ClassicalFlag.block (tangentHamiltonian β q) (tangentHamiltonian β q) +
          fromBlocks 0 0 0 ((M : ℂ) • (1 : Mat (Fin e.b))))
        (evolve U (ClassicalFlag.block (((1-p : ℝ) : ℂ) • bodyOutput e t) ((p : ℂ) • bodyOutput e t)) -
          ClassicalFlag.block (((1-p : ℝ) : ℂ) • e.source.matrix) ((p : ℂ) • e.source.matrix)) := by
  rw [physicalLinearized]
  rw [thermalBodyContact_handoff e p hp hp1 U hU t]
  rw [flagReference_tangent_gap β hβ q hq p hp hp1 M hgap]
  rw [thermalBodyContact_bodyOutput e p hp hp1 U hU t]
  have hsource : (thermalBodyContact e p hp hp1 U hU).source.matrix =
      (ClassicalFlag.block (((1-p : ℝ) : ℂ) • e.source.matrix) ((p : ℂ) • e.source.matrix)).submatrix
        (finSumFinEquiv.symm : Fin (e.b+e.b) ≃ Fin e.b ⊕ Fin e.b) finSumFinEquiv.symm := rfl
  rw [hsource]
  let X : Mat (Fin e.b ⊕ Fin e.b) := evolve U
    (ClassicalFlag.block (((1-p : ℝ) : ℂ) • bodyOutput e t) ((p : ℂ) • bodyOutput e t))
  let Y : Mat (Fin e.b ⊕ Fin e.b) :=
    ClassicalFlag.block (((1-p : ℝ) : ℂ) • e.source.matrix) ((p : ℂ) • e.source.matrix)
  let G : Mat (Fin e.b ⊕ Fin e.b) :=
    ClassicalFlag.block (tangentHamiltonian β q) (tangentHamiltonian β q) +
      fromBlocks 0 0 0 ((M : ℂ) • (1 : Mat (Fin e.b)))
  change handoff e t + energy
    ((G+(((-Real.log (1-p)/β : ℝ) : ℂ) • 1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    ((X-Y).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = handoff e t+energy G (X-Y)
  rw [energy_reindex (finSumFinEquiv.symm : Fin (e.b+e.b) ≃ Fin e.b ⊕ Fin e.b),energy_add]
  rw [energy_identity_trace_zero _ _
    (evolve_trace_one U _ hU (flag_input_trace _ (bodyOutput_density e t).2 p))
    (flag_input_trace _ e.source.normalized p)]
  ring

end ScheduleLaw.Blueprint
