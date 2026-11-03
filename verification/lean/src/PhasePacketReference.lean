import PhasePacketMap
import PhaseProductOverlap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhasePacketReference
open PhaseVectorDistance PhaseReferenceBound PhasePacketMap PhaseTensorVectors
variable {a p r : Type} [Fintype a] [Fintype p] [Fintype r]
  [DecidableEq a] [DecidableEq p] [DecidableEq r]

def coeff (ψ : a × r → ℂ) : Matrix a r ℂ := fun i j => ψ (i,j)

def lift (v : p → ℂ) (ψ : a × r → ℂ) : (a × p) × r → ℂ :=
  fun x => ψ (x.1.1,x.2)*v x.1.2

def wires : (a × p) × r ≃ (a × r) × p where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev mmul {m n k : Type} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n k ℂ) : Matrix m k ℂ :=
  @HMul.hMul (Matrix m n ℂ) (Matrix n k ℂ) (Matrix m k ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B


theorem lift_norm (v : p → ℂ) (ψ : a × r → ℂ) :
    ‖vector (lift v ψ)‖=‖vector ψ‖*‖vector v‖ := by
  calc _ = ‖vector (tensor ψ v)‖ := PhaseProductOverlap.norm_reindex wires (tensor ψ v)
       _ = _ := tensor_norm _ _

theorem action (V : Mat (a × p)) (v : p → ℂ) (ψ : a × r → ℂ) :
    (V ⊗ₖ (1 : Mat r)) *ᵥ lift v ψ=
      fun x : (a × p) × r => (mmul (mmul V (embed v)) (coeff ψ)) x.1 x.2 := by
  funext x
  simp only [Matrix.mulVec,dotProduct,kroneckerMap_apply,Matrix.one_apply,lift,
    Matrix.mul_apply,embed,coeff,Fintype.sum_prod_type]
  simp [mul_ite,ite_mul,apply_ite,Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm]

theorem vector_error (V : Mat (a × p)) (U : Mat a) (v : p → ℂ) (ψ : a × r → ℂ)
    (hψ : ‖vector ψ‖=1) :
    ‖vector ((V ⊗ₖ (1 : Mat r)) *ᵥ lift v ψ)-
      vector (((U ⊗ₖ (1 : Mat p)) ⊗ₖ (1 : Mat r)) *ᵥ lift v ψ)‖≤
        ‖(mmul V (embed v)-mmul (embed v) U : Matrix (a × p) a ℂ)‖ := by
  rw [action,action]
  have hJ : mmul (U ⊗ₖ (1 : Mat p)) (embed v)=mmul (embed v) U := by
    ext ⟨i,x⟩ j
    simp [mmul,Matrix.mul_apply,embed,kroneckerMap_apply,Matrix.one_apply,Fintype.sum_prod_type,
      ite_mul,mul_ite,mul_assoc,mul_comm,mul_left_comm]
  have he : (mmul (mmul V (embed v)) (coeff ψ))-
      (mmul (mmul (U ⊗ₖ (1 : Mat p)) (embed v)) (coeff ψ))=
        mmul (mmul V (embed v)-mmul (embed v) U) (coeff ψ) := by
    rw [hJ]
    ext i j
    simp only [mmul,Matrix.mul_apply,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  have hv : vector (fun x : (a × p) × r => mmul (mmul V (embed v)) (coeff ψ) x.1 x.2)-
      vector (fun x : (a × p) × r => mmul (mmul (U ⊗ₖ (1 : Mat p)) (embed v)) (coeff ψ) x.1 x.2)=
        vector (fun x : (a × p) × r => (mmul (mmul V (embed v)) (coeff ψ)-
          mmul (mmul (U ⊗ₖ (1 : Mat p)) (embed v)) (coeff ψ)) x.1 x.2) := by
    apply WithLp.ofLp_injective 2
    funext x
    rfl
  rw [hv,he,vector_matrix_norm]
  have hn : ‖coeff ψ‖=1 := by rw [← vector_matrix_norm]; exact hψ
  exact (Matrix.frobenius_norm_mul _ _).trans (by rw [hn,mul_one])

theorem pure_error (V : Mat (a × p)) (hV : IsUnitary V) (U : Mat a) (hU : IsUnitary U)
    (v : p → ℂ) (hv : ‖vector v‖=1) (ψ : a × r → ℂ) (hψ : ‖vector ψ‖=1) :
    traceDistance (pureMatrix ((V ⊗ₖ (1 : Mat r)) *ᵥ lift v ψ))
      (pureMatrix (((U ⊗ₖ (1 : Mat p)) ⊗ₖ (1 : Mat r)) *ᵥ lift v ψ))≤
        ‖(mmul V (embed v)-mmul (embed v) U : Matrix (a × p) a ℂ)‖ := by
  have hr : IsUnitary (1 : Mat r) := by constructor <;> simp
  have hp : IsUnitary (1 : Mat p) := by constructor <;> simp
  have hn : ‖vector (lift v ψ)‖=1 := by rw [lift_norm,hv,hψ,mul_one]
  exact (pure_distance _ _
    ((norm_unitary _ (unitary_kron hV hr) _).trans hn)
    ((norm_unitary _ (unitary_kron (unitary_kron hU hp) hr) _).trans hn)).trans
      (vector_error V U v ψ hψ)

end ScheduleLaw.Blueprint.PhasePacketReference
