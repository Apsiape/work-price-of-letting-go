import FlatOutput
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FiniteFlat

theorem projection_basis (d k : ℕ) (Q : Mat (Fin d)) (hQ : Q.IsHermitian)
    (hQi : Q*Q=Q) (hkd : k ≤ d) (htr : Q.trace=(k : ℂ)) :
    ∃ V : Mat (Fin d), IsUnitary V ∧ evolve V (rankProjection d k)=Q := by
  classical
  let E := hQ.eigenvectorUnitary
  let D : Mat (Fin d) := diagonal (fun i => (hQ.eigenvalues i : ℂ))
  let φ := Unitary.conjStarAlgAut ℂ (Mat (Fin d)) E
  have hφ : φ D=Q := hQ.spectral_theorem.symm
  have hD : D*D=D := by
    apply φ.injective
    have hφr : φ.toRingEquiv D=Q := hφ
    simpa only [map_mul,hφr] using hQi
  have h01 (i : Fin d) : hQ.eigenvalues i=0 ∨ hQ.eigenvalues i=1 := by
    have hh : (diagonal (fun i => (hQ.eigenvalues i : ℂ)))*
        (diagonal (fun i => (hQ.eigenvalues i : ℂ))) = diagonal (fun i => (hQ.eigenvalues i : ℂ)) := hD
    rw [diagonal_mul_diagonal] at hh
    have he:=congrArg (fun A : Mat (Fin d) => A i i) hh
    simp only [diagonal_apply_eq] at he
    have hr : hQ.eigenvalues i*hQ.eigenvalues i=hQ.eigenvalues i := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_mul] using he
    have hz : hQ.eigenvalues i*(hQ.eigenvalues i-1)=0 := by nlinarith only [hr]
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hsum : ∑ i,hQ.eigenvalues i=(k : ℝ) := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum,Complex.ofReal_natCast]
    exact hQ.trace_eq_sum_eigenvalues.symm.trans htr
  let p : Fin d → Prop := fun i => hQ.eigenvalues i=1
  have hcard : Fintype.card {i : Fin d // p i}=k := by
    have hc : (Fintype.card {i : Fin d // p i} : ℝ)=∑ i,hQ.eigenvalues i := by
      rw [Fintype.card_subtype,Finset.card_eq_sum_ones]
      simp only [Nat.cast_sum,Nat.cast_one]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rcases h01 i with h0 | h1
      · simp [p,h0]
      · simp [p,h1]
    exact_mod_cast hc.trans hsum
  have hcard0 : Fintype.card {i : Fin d // ¬p i}=d-k := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,hcard]
  let e1 : {i : Fin d // p i} ≃ Fin k := (Fintype.equivFin _).trans (finCongr hcard)
  let e0 : {i : Fin d // ¬p i} ≃ Fin (d-k) := (Fintype.equivFin _).trans (finCongr hcard0)
  let e : Equiv.Perm (Fin d) := (Equiv.sumCompl p).symm.trans
    ((Equiv.sumCongr e1 e0).trans (finSumFinEquiv.trans (finCongr (by omega))))
  have he (i : Fin d) : (e i).val<k ↔ p i := by
    by_cases hp : p i
    · have hv : (e i).val=(e1 ⟨i,hp⟩).val := by simp [e,hp]
      have hl : (e i).val<k := by rw [hv]; exact (e1 ⟨i,hp⟩).isLt
      exact ⟨fun _ => hp,fun _ => hl⟩
    · have hv : (e i).val=k+(e0 ⟨i,hp⟩).val := by simp [e,hp]
      have hl : ¬(e i).val<k := by rw [hv]; omega
      exact ⟨fun h => False.elim (hl h),fun h => False.elim (hp h)⟩
  have hP : evolve (e.permMatrix ℂ) (rankProjection d k)=D := by
    rw [rankProjection,FlatOutput.permutation_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    by_cases hp : p i
    · simp only [if_pos ((he i).mpr hp)]
      exact_mod_cast hp.symm
    · rcases h01 i with h0 | h1
      · simp [h0,show ¬(e i).val<k from fun h => hp ((he i).mp h)]
      · exact False.elim (hp h1)
  have hE : IsUnitary (E : Mat (Fin d)) := E.property
  refine ⟨(E : Mat (Fin d))*e.permMatrix ℂ,unitary_mul hE (Recorder.permutation_unitary e),?_⟩
  calc evolve ((E : Mat (Fin d))*e.permMatrix ℂ) (rankProjection d k) =
      evolve (E : Mat (Fin d)) (evolve (e.permMatrix ℂ) (rankProjection d k)) := by
        simp only [evolve,conjTranspose_mul,mul_assoc]
       _ = evolve (E : Mat (Fin d)) D := congrArg (evolve (E : Mat (Fin d))) hP
       _ = Q := hφ
end ScheduleLaw.Blueprint.FiniteFlat
