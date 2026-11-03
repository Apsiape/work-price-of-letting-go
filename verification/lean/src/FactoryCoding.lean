import BoundedSourceCoding
import BlueprintFinitePrimitives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCoding
open History

theorem projection_positive {a : Type} [Fintype a] [DecidableEq a]
    (P : Mat a) (hP : P.IsHermitian) (hPi : P*P=P) : P.PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self P
  rwa [hP.eq,hPi] at h

theorem complement_positive {a : Type} [Fintype a] [DecidableEq a]
    (P : Mat a) (hP : P.IsHermitian) (hPi : P*P=P) : (1-P).PosSemidef := by
  have he : (1-P)ᴴ*(1-P)=1-P := by
    simp only [conjTranspose_sub,conjTranspose_one,hP.eq,mul_sub,sub_mul,
      one_mul,mul_one,hPi]
    abel
  have h := posSemidef_conjTranspose_mul_self (1-P)
  rwa [he] at h

theorem rank_bound {a : Type} [Fintype a] [DecidableEq a]
    (P : Mat a) (hP : P.IsHermitian) (hPi : P*P=P) (K : ℕ) (htr : P.trace=(K : ℂ)) :
    K≤Fintype.card a := by
  have ht := (complement_positive P hP hPi).trace_nonneg
  rw [trace_sub,trace_one,htr] at ht
  have hr := (Complex.nonneg_iff.mp ht).1
  simp only [Complex.sub_re,Complex.natCast_re] at hr
  exact_mod_cast (sub_nonneg.mp hr)

def flatDensity {a : Type} [Fintype a] [DecidableEq a]
    (P : Mat a) (hP : P.IsHermitian) (hPi : P*P=P) (K : ℕ) (hK : 0<K)
    (htr : P.trace=(K : ℂ)) : Density a :=
  ⟨((K : ℂ)⁻¹) • P,by
    have he : ((K : ℂ)⁻¹) • P = (K : ℝ)⁻¹ • P := by
      ext i j
      simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,
        Complex.ofReal_inv,Complex.ofReal_natCast]
    rw [he]
    exact (projection_positive P hP hPi).smul (by positivity : 0≤(K : ℝ)⁻¹),by
    rw [trace_smul,htr,smul_eq_mul,inv_mul_cancel₀ (by exact_mod_cast hK.ne')]⟩

theorem physical_flat_stage {a : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    (β : ℝ) (hβ : 0<β) (P : Mat a) (hP : P.IsHermitian) (hPi : P*P=P)
    (K : ℕ) (hK : 0<K) (htr : P.trace=(K : ℂ)) (f : ℝ) (hf : 0<f) :
    let D := Fintype.card a
    let e := (Fintype.equivFin a).symm
    ∃ C : SupportConverter β (FiniteFlat.zeroHamiltonian D) (-Real.log ((D : ℝ)/K)/β),
      ∃ p : ℝ,1-f≤p ∧ p≤1 ∧
        FiniteFlat.flatOutput C = ((p/(K : ℝ) : ℂ) • P.submatrix e e) := by
  dsimp only
  let e := (Fintype.equivFin a).symm
  have hPi' : (P.submatrix e e)*(P.submatrix e e)=P.submatrix e e := by
    rw [submatrix_mul_equiv,hPi]
  have htr' : (P.submatrix e e).trace=(K : ℂ) := by rw [submatrix_trace_equiv,htr]
  obtain ⟨C,p,hp,hp1,hout⟩ := FiniteFlat.exact_flat Fintype.card_pos β hβ
    (P.submatrix e e) (hP.submatrix e) hPi' K hK (rank_bound P hP hPi K htr) htr' f hf
  refine ⟨C,p,hp,hp1,?_⟩
  simpa only [FiniteFlat.flatOutput,Complex.ofReal_div,Complex.ofReal_natCast] using hout

end ScheduleLaw.Blueprint.FactoryCoding
