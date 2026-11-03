import FactoryCodingOutput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCodingSuccess
open History

/-- Retain the actual success marginal and unconditional output accuracy of
one and the same constructed flat converter. -/
theorem coding_output {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (τ : Density (Fin d)) (C : SmallResidueCoding τ) (n : ℕ) (f : ℝ) (hf : 0 < f) :
    let a := (Fin (n+1) → Fin d) × Fin (C.residue n)
    let D := Fintype.card a
    let e := Fintype.equivFin a
    let hD : 0 < D := by
      letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
      letI : Nonempty (Fin (C.residue n)) := ⟨⟨0,C.residue_pos n⟩⟩
      exact Fintype.card_pos
    ∃ A : SupportConverter β (FiniteFlat.zeroHamiltonian D)
      (-Real.log ((D : ℝ)/C.rank n)/β),
      let st := FactoryFlatRun.state A (FactoryFormation.flat D hD)
      1-f ≤ energy ((1 : Mat (Fin D)) ⊗ₖ
        (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin A.r)))) st.matrix ∧
      traceDistance (partialRight (evolve (C.unitary n)
        ((partialRight st.matrix).submatrix e e)))
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
  have hprob : energy ((1 : Mat (Fin D)) ⊗ₖ
      (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin A.r)))) st.matrix=p := by
    unfold energy
    rw [← partialRight_trace,FactoryFlatRun.success_marginal,hs,trace_smul,
      submatrix_trace_equiv,σ.normalized]
    simp
  refine ⟨A,?_,?_⟩
  · rw [hprob]
    exact hp
  exact FactoryDecode.error (C.unitary n) (C.unitary_isUnitary n) ρ σ
    (tensorPower τ.matrix (n+1)) p (C.error n) f hp1 hp hg (C.approximation n)

end ScheduleLaw.Blueprint.FactoryCodingSuccess
