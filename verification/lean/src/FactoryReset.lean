import SupportHardware
import W2.UniformMarginal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryReset
open History

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def swap : Equiv.Perm (a × (b × a)) where
  toFun z := (z.2.2,(z.2.1,z.1))
  invFun z := (z.2.2,(z.2.1,z.1))
  left_inv _ := rfl
  right_inv _ := rfl

theorem unitary : IsUnitary ((swap (a:=a) (b:=b)).permMatrix ℂ) :=
  Recorder.permutation_unitary _

/-- The entire old controller, with all of its correlations, becomes part of
 the physical rest. The new controller is exactly the fresh stock. -/
theorem whole_rest_return (ρ : Mat (a × b)) (σ : Mat a) :
    evolve ((swap (a:=a) (b:=b)).permMatrix ℂ)
      ((ρ ⊗ₖ σ).submatrix (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm) =
      σ ⊗ₖ (ρ.submatrix (Equiv.prodComm b a) (Equiv.prodComm b a)) := by
  rw [Recorder.permutation_evolve]
  ext ⟨i,⟨r,k⟩⟩ ⟨j,⟨s,h⟩⟩
  change ρ (k,r) (h,s)*σ i j = σ i j*ρ (k,r) (h,s)
  ring

theorem controller_marginal (ρ : Density (a × b)) (σ : Density a) :
    partialRight (evolve ((swap (a:=a) (b:=b)).permMatrix ℂ)
      ((ρ.matrix ⊗ₖ σ.matrix).submatrix
        (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm)) = σ.matrix := by
  rw [whole_rest_return,partialRight_kron,submatrix_trace_equiv,ρ.normalized,one_smul]

theorem rest_marginal (ρ : Density (a × b)) (σ : Density a) :
    partialLeft (evolve ((swap (a:=a) (b:=b)).permMatrix ℂ)
      ((ρ.matrix ⊗ₖ σ.matrix).submatrix
        (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm)) =
      ρ.matrix.submatrix (Equiv.prodComm b a) (Equiv.prodComm b a) := by
  rw [whole_rest_return,partialLeft_kron,σ.normalized,one_smul]

theorem product_defect_zero (ρ : Density (a × b)) (σ : Density a) :
    let O := evolve ((swap (a:=a) (b:=b)).permMatrix ℂ)
      ((ρ.matrix ⊗ₖ σ.matrix).submatrix
        (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm)
    traceDistance O (σ.matrix ⊗ₖ partialLeft O) = 0 := by
  dsimp only
  rw [rest_marginal,whole_rest_return]
  exact W2.traceDistance_self _

/-- A zero-Hamiltonian reset stock does not change the Hamiltonian of the
 arbitrary retained rest, including all retired baths. -/
theorem conserves_rest (K : Mat b) :
    Conserves ((swap (a:=a) (b:=b)).permMatrix ℂ)
      ((1 : Mat a) ⊗ₖ (K ⊗ₖ (1 : Mat a))) := by
  have hstar : ((swap (a:=a) (b:=b)).permMatrix ℂ)ᴴ =
      (swap (a:=a) (b:=b)).permMatrix ℂ := by
    rw [conjTranspose_permMatrix]
    rfl
  unfold Conserves
  rw [hstar]
  have he := Recorder.permutation_evolve (swap (a:=a) (b:=b))
    ((1 : Mat a) ⊗ₖ (K ⊗ₖ (1 : Mat a)))
  simp only [evolve,hstar] at he
  rw [he]
  ext ⟨i,⟨r,k⟩⟩ ⟨j,⟨s,h⟩⟩
  simp only [submatrix_apply,swap,Equiv.coe_fn_mk,kroneckerMap_apply,one_apply]
  split_ifs <;> ring

end ScheduleLaw.Blueprint.FactoryReset
