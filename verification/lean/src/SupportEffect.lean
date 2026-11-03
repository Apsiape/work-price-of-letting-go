import FiniteConverterModel
import RareHistoryEffect
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder RealInnerProductSpace
namespace ScheduleLaw.Blueprint.SupportEffect

theorem positive_energy {a : Type} [Fintype a] [DecidableEq a]
    (A ρ : Mat a) (hA : A.PosSemidef) (hρ : ρ.PosSemidef) : 0≤energy A ρ := by
  let AH : HermitianMat a ℂ := ⟨A,hA.isHermitian⟩
  let RH : HermitianMat a ℂ := ⟨ρ,hρ.isHermitian⟩
  have h := HermitianMat.inner_ge_zero (A:=AH) (B:=RH)
    (HermitianMat.zero_le_iff.mpr hA) (HermitianMat.zero_le_iff.mpr hρ)
  exact h

theorem energy_mono {a : Type} [Fintype a] [DecidableEq a]
    (A B ρ : Mat a) (hgap : (A-B).PosSemidef) (hρ : ρ.PosSemidef) :
    energy B ρ≤energy A ρ := by
  have h := positive_energy (A-B) ρ hgap hρ
  simp only [energy,sub_mul,trace_sub,Complex.sub_re] at h ⊢
  linarith

/-- A single operator lower bound proves the same probability bound for every
coherent input and every finite reference. No input state is diagonalized. -/
theorem reference_uniform_bound {a z : Type} [Fintype a] [Fintype z]
    [DecidableEq a] [DecidableEq z] (A P : Mat a) (c : ℝ)
    (hgap : (A-(c : ℂ) • P).PosSemidef) (ρ : Density (a × z))
    (hsupport : (P ⊗ₖ (1 : Mat z))*ρ.matrix=ρ.matrix) :
    c≤energy (A ⊗ₖ (1 : Mat z)) ρ.matrix := by
  have hfull : ((A ⊗ₖ (1 : Mat z))-(c : ℂ) • (P ⊗ₖ (1 : Mat z))).PosSemidef := by
    have heq : (A-(c : ℂ) • P) ⊗ₖ (1 : Mat z) =
        (A ⊗ₖ (1 : Mat z))-(c : ℂ) • (P ⊗ₖ (1 : Mat z)) := by
      ext ⟨i,k⟩ ⟨j,l⟩
      simp only [kroneckerMap_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      ring
    rw [← heq]
    exact hgap.kronecker (Matrix.PosSemidef.one : (1 : Mat z).PosSemidef)
  have h := energy_mono (A ⊗ₖ (1 : Mat z)) ((c : ℂ) • (P ⊗ₖ (1 : Mat z))) ρ.matrix hfull ρ.positive
  have hp : energy (P ⊗ₖ (1 : Mat z)) ρ.matrix=1 := by
    rw [energy,hsupport,ρ.normalized]
    rfl
  rw [ScheduleLaw.History.energy_observable_weight,hp,mul_one] at h
  exact h

end ScheduleLaw.Blueprint.SupportEffect
