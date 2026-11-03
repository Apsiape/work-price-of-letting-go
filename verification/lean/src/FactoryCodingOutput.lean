import FactoryFlatRun
import FactoryDecode

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCodingOutput
open History

/-- The actual flat converter, including every failure column, followed by the
actual spectral decoder emits an unconditional approximate tensor-power batch.
No postselection and no independence of the coding residue is asserted. -/
theorem coding_output {d : ℕ} (hd : 0<d) (β : ℝ) (hβ : 0<β)
    (τ : Density (Fin d)) (C : SmallResidueCoding τ) (n : ℕ) (f : ℝ) (hf : 0<f) :
    let a := (Fin (n+1) → Fin d) × Fin (C.residue n)
    let D := Fintype.card a
    let e := Fintype.equivFin a
    ∃ A : SupportConverter β (FiniteFlat.zeroHamiltonian D)
      (-Real.log ((D : ℝ)/C.rank n)/β),
      traceDistance (partialRight (evolve (C.unitary n)
        ((partialRight (FactoryFlatRun.state A (FactoryFormation.flat D
          (by
            letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
            letI : Nonempty (Fin (C.residue n)) := ⟨⟨0,C.residue_pos n⟩⟩
            exact Fintype.card_pos))).matrix).submatrix e e)))
        (tensorPower τ.matrix (n+1))≤C.error n+f := by
  classical
  dsimp only
  let a := (Fin (n+1) → Fin d) × Fin (C.residue n)
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin (C.residue n)) := ⟨⟨0,C.residue_pos n⟩⟩
  let D := Fintype.card a
  let e := Fintype.equivFin a
  have hD : 0<D := Fintype.card_pos
  obtain ⟨A,p,hp,hp1,hout⟩ := FactoryCoding.physical_flat_stage β hβ (C.projection n)
    (C.projection_hermitian n) (C.projection_idempotent n) (C.rank n) (C.rank_pos n)
    (C.projection_trace n) f hf
  let st := FactoryFlatRun.state A (FactoryFormation.flat D hD)
  let ρ : Density a := ⟨(partialRight st.matrix).submatrix e e,
    (partialRight_positive st.positive).submatrix _,by
      rw [submatrix_trace_equiv,partialRight_trace,st.normalized]⟩
  let σ := FactoryCoding.flatDensity (C.projection n) (C.projection_hermitian n)
    (C.projection_idempotent n) (C.rank n) (C.rank_pos n) (C.projection_trace n)
  have hs : FactoryOutput.branch st.matrix 1=
      (p : ℂ) • σ.matrix.submatrix e.symm e.symm := by
    rw [show FactoryOutput.branch st.matrix 1=FiniteFlat.flatOutput A from
      (FactoryFlatRun.flatOutput_eq_branch A hD).symm,hout]
    ext i j
    simp only [σ,FactoryCoding.flatDensity,Matrix.submatrix_apply,Matrix.smul_apply,
      smul_eq_mul,Complex.ofReal_natCast,div_eq_mul_inv]
    ring
  have hg := (FactoryOutput.marginal_dominates st.matrix st.positive).submatrix e
  have he : (partialRight st.matrix-FactoryOutput.branch st.matrix 1).submatrix e e =
      ρ.matrix-(p : ℂ) • σ.matrix := by
    rw [hs]
    ext i j
    simp only [ρ,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,
      Equiv.symm_apply_apply]
  rw [he] at hg
  refine ⟨A,?_⟩
  exact FactoryDecode.error (C.unitary n) (C.unitary_isUnitary n) ρ σ
    (tensorPower τ.matrix (n+1)) p (C.error n) f hp1 hp hg (C.approximation n)

end ScheduleLaw.Blueprint.FactoryCodingOutput
