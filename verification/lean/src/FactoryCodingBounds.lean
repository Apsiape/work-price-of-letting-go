import FactoryUniformBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryCodingBounds
open History

def gapConstant (β : ℝ) (d : ℕ) (Λ : ℝ) : ℝ := 3*Λ+(2*Real.log (d : ℝ)+1)/β+2
def constant (β : ℝ) (d : ℕ) (Λ : ℝ) : ℝ := gapConstant β d Λ+4*Λ

theorem gapConstant_nonneg (β : ℝ) (hβ : 0 < β) (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) : 0 ≤ gapConstant β d Λ := by
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  unfold gapConstant
  positivity

theorem log_dimension {d R m : ℕ} (hd : 0 < d) (hR : 0 < R) :
    Real.log (Fintype.card ((Fin m → Fin d) × Fin R) : ℝ)=
      (m : ℝ)*Real.log (d : ℝ)+Real.log (R : ℝ) := by
  have he : (Fintype.card ((Fin m → Fin d) × Fin R) : ℝ)=(d : ℝ)^m*(R : ℝ) := by
    simp [Fintype.card_fun]
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow]

theorem gap_bound {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (τ : Density (Fin d)) (C : SmallResidueCoding τ) (n : ℕ)
    (Λ Eg Ecode : ℝ) (hΛ : 0 ≤ Λ)
    (hR : Real.log (C.residue n : ℝ) ≤ (n+1 : ℝ))
    (hEg : |Eg| ≤ (n+1 : ℝ)*Λ) (hEc : |Ecode| ≤ (n+1 : ℝ)*Λ) :
    let D := Fintype.card ((Fin (n+1) → Fin d) × Fin (C.residue n))
    |-Eg-1|+|-Real.log ((D : ℝ)/C.rank n)/β|+|Eg-Ecode|+
      |Real.log ((D : ℝ)/C.residue n)/β-1| ≤ (n+1 : ℝ)*gapConstant β d Λ := by
  dsimp only
  let D := Fintype.card ((Fin (n+1) → Fin d) × Fin (C.residue n))
  have hK : (0 : ℝ)<C.rank n := by exact_mod_cast C.rank_pos n
  have hres : (0 : ℝ)<C.residue n := by exact_mod_cast C.residue_pos n
  have hKD : (C.rank n : ℝ) ≤ D := by
    exact_mod_cast FactoryCoding.rank_bound (C.projection n) (C.projection_hermitian n)
      (C.projection_idempotent n) (C.rank n) (C.projection_trace n)
  have hD : (0 : ℝ)<D := hK.trans_le hKD
  rw [Real.log_div hD.ne' hK.ne',Real.log_div hD.ne' hres.ne']
  apply FactoryUniformBounds.gap_sum β (n+1 : ℝ) (Real.log (d : ℝ)) Λ
    (Real.log (D : ℝ)) (Real.log (C.rank n : ℝ)) (Real.log (C.residue n : ℝ)) Eg Ecode
    hβ (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    (Real.log_nonneg (by exact_mod_cast hd)) hΛ
    (Real.log_nonneg (by exact_mod_cast C.rank_pos n)) (Real.log_le_log hK hKD) hR
    (by simpa only [Nat.cast_add,Nat.cast_one] using log_dimension (m:=n+1) hd (C.residue_pos n)) hEg hEc

end ScheduleLaw.Blueprint.FactoryCodingBounds


