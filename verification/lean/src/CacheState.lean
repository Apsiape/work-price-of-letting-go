import BlueprintFactory
import W2.TensorFamily
import BlueprintHeatEffect

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- Actual cyclic-cache data in a tensor-power basis. -/
def cacheState {d : ℕ} (τ q : Density (Fin d)) (m : ℕ) :
    Mat (Fin m × (Fin (m-1) → Fin d)) := fun i j =>
  if i.1=j.1 then ((m : ℂ)⁻¹) * ∏ k,
    (if k.val < i.1.val then τ.matrix else q.matrix) (i.2 k) (j.2 k) else 0

theorem cache_density {d : ℕ} (τ q : Density (Fin d)) (m : ℕ) (hm : 0 < m) :
    (cacheState τ q m).PosSemidef ∧ (cacheState τ q m).trace=1 := by
  classical
  let ρ (c : Fin m) : Density (Fin (m-1) → Fin d) :=
    W2.tensorFamilyDensity (fun k => if k.val < c.val then τ else q)
  let E (c : Fin m) : Mat (Fin m) := diagonal (fun j => if j=c then 1 else 0)
  let A (c : Fin m) : Mat (Fin m × (Fin (m-1) → Fin d)) := E c ⊗ₖ (ρ c).matrix
  have hE (c : Fin m) : (E c).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hj : j=c <;> simp [hj]
  have hEt (c : Fin m) : (E c).trace=1 := by
    simp [E]
  have hAt (c : Fin m) : (A c).trace=1 := by
    change (E c ⊗ₖ (ρ c).matrix).trace=1
    rw [trace_kronecker,hEt,(ρ c).normalized,one_mul]
  have heq : cacheState τ q m = ((m : ℝ)⁻¹) • (∑ c : Fin m, A c) := by
    ext ⟨a,u⟩ ⟨b,v⟩
    by_cases hab : a=b
    · subst b
      simp [cacheState,A,E,ρ,W2.tensorFamilyDensity,W2.tensorFamily,
        Matrix.diagonal,Matrix.sum_apply,Matrix.kroneckerMap_apply,Matrix.of_apply,
        apply_ite,ite_mul,mul_ite,eq_comm,Complex.real_smul,hm.ne']
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hka : k.val < a.val <;> simp [hka]
    · simp [cacheState,A,E,ρ,W2.tensorFamilyDensity,W2.tensorFamily,
        Matrix.diagonal,Matrix.sum_apply,Matrix.kroneckerMap_apply,Matrix.of_apply,
        apply_ite,ite_mul,mul_ite,hab,Complex.real_smul,hm.ne']
  constructor
  · rw [heq]
    exact (Matrix.posSemidef_sum Finset.univ
      (fun c _ => (hE c).kronecker (ρ c).positive)).smul (by positivity : 0 ≤ (m : ℝ)⁻¹)
  · rw [heq,trace_smul,trace_sum]
    simp only [hAt,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one]
    simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (by exact_mod_cast hm.ne')


end ScheduleLaw.Blueprint
