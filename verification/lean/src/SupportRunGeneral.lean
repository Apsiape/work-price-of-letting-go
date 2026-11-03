import SupportRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportRun
open History

/-- A retained operator certificate for the constructed physical converter.
It is data proved by the finite construction, rather than an added premise of
the original support-conversion theorem. -/
def EffectCertificate {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (P Q : Mat (Fin d)) (f : ℝ) : Prop :=
  ∃ G : Mat (Fin C.r),
    (C.Uᴴ*(Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U -
      P ⊗ₖ (level 0 ⊗ₖ G)).PosSemidef ∧
    1-f ≤ energy G (gibbs β C.HR)

theorem hermitian_trace_mul_real {a : Type} [Fintype a] [DecidableEq a]
    (A B : Mat a) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A*B).trace.im=0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (A*B).trace=(A*B).trace
  rw [← trace_conjTranspose,conjTranspose_mul,hB.eq,hA.eq,trace_mul_comm]

/-- The initializer factors even if the source has weight outside P. -/
theorem initialized_product {d r z : ℕ} (P : Mat (Fin d)) (G γ : Mat (Fin r))
    (hP : P.IsHermitian) (ρ : Density (Fin d × Fin z)) :
    energy ((P ⊗ₖ (level 0 ⊗ₖ G)) ⊗ₖ (1 : Mat (Fin z)))
      ((ρ.matrix ⊗ₖ (level 0 ⊗ₖ γ)).submatrix
        (converterFrame d r z).symm (converterFrame d r z).symm) =
      energy (P ⊗ₖ (1 : Mat (Fin z))) ρ.matrix * energy G γ := by
  have he : ((P ⊗ₖ (level 0 ⊗ₖ G)) ⊗ₖ (1 : Mat (Fin z))) =
      (((P ⊗ₖ (1 : Mat (Fin z))) ⊗ₖ (level 0 ⊗ₖ G)).submatrix
        (converterFrame d r z).symm (converterFrame d r z).symm) := by
    ext ⟨⟨i,⟨w,b⟩⟩,k⟩ ⟨⟨j,⟨v,c⟩⟩,h⟩
    simp only [submatrix_apply,converterFrame,Equiv.coe_fn_symm_mk,
      kroneckerMap_apply]
    ring
  rw [he,energy_reindex]
  unfold energy
  rw [← mul_kronecker_mul,trace_kronecker,← mul_kronecker_mul,
    trace_kronecker,level_idem,level_trace,one_mul,Complex.mul_re]
  rw [hermitian_trace_mul_real _ _ (by
    simp only [Matrix.IsHermitian,conjTranspose_kronecker,conjTranspose_one,hP.eq])
    ρ.positive.isHermitian]
  ring

/-- Reference-uniform lower bound with the actual input support weight. -/
theorem probability_general {d : ℕ} {β x : ℝ} {H : Hamiltonian (Fin d)}
    (C : SupportConverter β H x) (P Q : Mat (Fin d)) (G : Mat (Fin C.r))
    (hP : P.IsHermitian)
    (hgap : (C.Uᴴ*(Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U -
      P ⊗ₖ (level 0 ⊗ₖ G)).PosSemidef)
    (z : ℕ) (ρ : Density (Fin d × Fin z)) :
    energy (P ⊗ₖ (1 : Mat (Fin z))) ρ.matrix * energy G (gibbs β C.HR) ≤
      energy ((Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  letI : Nonempty (Fin C.r) := ⟨⟨0,C.r_pos⟩⟩
  let N := ((ρ.matrix ⊗ₖ (level 0 ⊗ₖ gibbs β C.HR)).submatrix
    (converterFrame d C.r z).symm (converterFrame d C.r z).symm)
  have hN : N.PosSemidef := (ρ.positive.kronecker
    ((pureMatrix_positive _).kronecker (gibbs_positive β C.HR))).submatrix _
  have hfull : (((C.Uᴴ*(Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U) ⊗ₖ
      (1 : Mat (Fin z))) - (P ⊗ₖ (level 0 ⊗ₖ G)) ⊗ₖ (1 : Mat (Fin z))).PosSemidef := by
    convert hgap.kronecker (Matrix.PosSemidef.one : (1 : Mat (Fin z)).PosSemidef) using 1
    ext ⟨i,k⟩ ⟨j,l⟩
    simp only [kroneckerMap_apply,Matrix.sub_apply]
    ring
  have hm := SupportEffect.energy_mono _ _ N hfull hN
  rw [initialized_product P G (gibbs β C.HR) hP ρ] at hm
  unfold SupportConverter.run
  rw [energy_pullback]
  simpa only [conjTranspose_kronecker,conjTranspose_one,← mul_kronecker_mul,
    one_mul,mul_one] using hm

theorem EffectCertificate.general {d : ℕ} {β x f : ℝ} {H : Hamiltonian (Fin d)}
    {C : SupportConverter β H x} {P Q : Mat (Fin d)}
    (hc : EffectCertificate C P Q f) (hP : P.PosSemidef)
    (z : ℕ) (ρ : Density (Fin d × Fin z)) :
    (1-f)*energy (P ⊗ₖ (1 : Mat (Fin z))) ρ.matrix ≤
      energy ((Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  obtain ⟨G,hgap,hstock⟩ := hc
  have hp := SupportEffect.positive_energy _ _
    (hP.kronecker Matrix.PosSemidef.one) ρ.positive
  exact (mul_le_mul_of_nonneg_right hstock hp).trans
    (by simpa only [mul_comm] using probability_general C P Q G hP.isHermitian hgap z ρ)

theorem EffectCertificate.supported {d : ℕ} {β x f : ℝ} {H : Hamiltonian (Fin d)}
    {C : SupportConverter β H x} {P Q : Mat (Fin d)}
    (hc : EffectCertificate C P Q f) (z : ℕ) (ρ : Density (Fin d × Fin z))
    (hρ : (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix) :
    1-f ≤ energy ((Q ⊗ₖ (level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
      (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  obtain ⟨G,hgap,hstock⟩ := hc
  exact hstock.trans (probability C P Q G hgap z ρ hρ)

end ScheduleLaw.Blueprint.SupportRun
