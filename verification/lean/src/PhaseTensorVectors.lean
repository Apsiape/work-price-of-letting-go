import PhaseVectorDistance

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseTensorVectors
open PhaseVectorDistance
variable {a b : Type} [Fintype a] [Fintype b]

def tensor (u : a → ℂ) (v : b → ℂ) : a × b → ℂ := fun x => u x.1*v x.2

theorem tensor_norm (u : a → ℂ) (v : b → ℂ) :
    ‖vector (tensor u v)‖=‖vector u‖*‖vector v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simp only [vector,tensor,PiLp.toLp_apply,norm_mul,mul_pow,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem tensor_difference (u u' : a → ℂ) (v v' : b → ℂ) :
    ‖vector (tensor u v)-vector (tensor u' v')‖ ≤
      ‖vector u-vector u'‖*‖vector v‖+‖vector u'‖*‖vector v-vector v'‖ := by
  have hh : vector (tensor u v)-vector (tensor u' v')=
      vector (tensor (u-u') v)+vector (tensor u' (v-v')) := by
    apply WithLp.ofLp_injective 2
    funext x
    change u x.1*v x.2-u' x.1*v' x.2=(u x.1-u' x.1)*v x.2+u' x.1*(v x.2-v' x.2)
    ring
  rw [hh]
  exact (norm_add_le _ _).trans (by
    rw [tensor_norm,tensor_norm]
    rfl)

end ScheduleLaw.Blueprint.PhaseTensorVectors
