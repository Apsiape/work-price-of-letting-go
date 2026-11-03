import PhasePacketReference
import PhaseDensityTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhasePacketMixed
open History PhaseVectorDistance PhasePacketReference
variable {a p r q : Type} [Fintype a] [Fintype p] [Fintype r] [Fintype q]
  [DecidableEq a] [DecidableEq p] [DecidableEq r] [DecidableEq q]

def attach (v : p → ℂ) (ρ : Mat (a × r)) : Mat ((a × p) × r) :=
  (ρ ⊗ₖ pureMatrix v).submatrix PhasePacketReference.wires PhasePacketReference.wires

def reassoc (ψ : (a × r) × q → ℂ) : a × (r × q) → ℂ :=
  fun x => ψ ((x.1,x.2.1),x.2.2)

theorem reduce_lift (v : p → ℂ) (ψ : (a × r) × q → ℂ) :
    partialRight ((pureMatrix (lift v (reassoc ψ))).submatrix
      (Equiv.prodAssoc (a × p) r q) (Equiv.prodAssoc (a × p) r q))=
        attach v (partialRight (pureMatrix ψ)) := by
  ext i j
  simp only [partialRight,submatrix_apply,pureMatrix,lift,reassoc,attach,PhasePacketReference.wires,
    Equiv.coe_fn_mk,Equiv.prodAssoc_apply,kroneckerMap_apply,star_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem gate_reindex (V : Mat (a × p)) :
    (V ⊗ₖ (1 : Mat (r × q))).submatrix (Equiv.prodAssoc (a × p) r q)
      (Equiv.prodAssoc (a × p) r q)=(V ⊗ₖ (1 : Mat r)) ⊗ₖ (1 : Mat q) := by
  ext ⟨⟨i,x⟩,z⟩ ⟨⟨j,y⟩,w⟩
  simp only [submatrix_apply,Equiv.prodAssoc_apply,kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq]
  by_cases hxy : x=y <;> by_cases hzw : z=w <;> simp [hxy,hzw]

theorem output_reduces (V : Mat (a × p)) (v : p → ℂ) (ψ : (a × r) × q → ℂ) :
    partialRight ((pureMatrix ((V ⊗ₖ (1 : Mat (r × q))) *ᵥ lift v (reassoc ψ))).submatrix
      (Equiv.prodAssoc (a × p) r q) (Equiv.prodAssoc (a × p) r q))=
        evolve (V ⊗ₖ (1 : Mat r)) (attach v (partialRight (pureMatrix ψ))) := by
  rw [pureMatrix_mulVec]
  change partialRight ((evolve (V ⊗ₖ (1 : Mat (r × q)))
    (pureMatrix (lift v (reassoc ψ)))).submatrix (Equiv.prodAssoc (a × p) r q)
      (Equiv.prodAssoc (a × p) r q))=_
  rw [← evolve_submatrix_equiv,gate_reindex,partialRight_evolve_kron_one,reduce_lift]

theorem attach_evolve (U : Mat a) (v : p → ℂ) (ρ : Mat (a × r)) :
    evolve ((U ⊗ₖ (1 : Mat p)) ⊗ₖ (1 : Mat r)) (attach v ρ)=
      attach v (evolve (U ⊗ₖ (1 : Mat r)) ρ) := by
  have hG : ((U ⊗ₖ (1 : Mat r)) ⊗ₖ (1 : Mat p)).submatrix
      PhasePacketReference.wires PhasePacketReference.wires=
        (U ⊗ₖ (1 : Mat p)) ⊗ₖ (1 : Mat r) := by
    ext i j
    simp only [submatrix_apply,PhasePacketReference.wires,Equiv.coe_fn_mk,kroneckerMap_apply]
    ring
  rw [← hG,attach,evolve_submatrix_equiv,IdleExtension.evolve_idle] <;> rfl


theorem channel (V : Mat (a × p)) (hV : IsUnitary V) (U : Mat a) (hU : IsUnitary U)
    (v : p → ℂ) (hv : ‖vector v‖=1) (ρ : Density (a × r)) :
    traceDistance (evolve (V ⊗ₖ (1 : Mat r)) (attach v ρ.matrix))
      (evolve ((U ⊗ₖ (1 : Mat p)) ⊗ₖ (1 : Mat r)) (attach v ρ.matrix))≤
        ‖(V*PhasePacketMap.embed v-PhasePacketMap.embed v*U : Matrix (a × p) a ℂ)‖ := by
  let ψ := ρ.toMState.purify.vec
  have hψ : ‖vector ψ‖=1 := by
    have hn := ρ.toMState.purify.normalized'
    have hs := EuclideanSpace.norm_sq_eq (vector ψ)
    simp only [vector,PiLp.toLp_apply] at hs
    change (∑ x,‖ψ x‖^2)=1 at hn
    rw [hn] at hs
    nlinarith [norm_nonneg (vector ψ)]
  have hr : ‖vector (reassoc ψ)‖=1 :=
    (PhaseProductOverlap.norm_reindex (Equiv.prodAssoc a r (a × r)).symm ψ).trans hψ
  have hp := pure_error V hV U hU v hv (reassoc ψ) hr
  have hc := TraceMarginal.right_distance
    ((pureMatrix ((V ⊗ₖ (1 : Mat (r × (a × r)))) *ᵥ lift v (reassoc ψ))).submatrix
      (Equiv.prodAssoc (a × p) r (a × r)) (Equiv.prodAssoc (a × p) r (a × r)))
    ((pureMatrix (((U ⊗ₖ (1 : Mat p)) ⊗ₖ (1 : Mat (r × (a × r)))) *ᵥ lift v (reassoc ψ))).submatrix
      (Equiv.prodAssoc (a × p) r (a × r)) (Equiv.prodAssoc (a × p) r (a × r)))
  rw [TraceMarginal.reindex_distance,output_reduces,output_reduces] at hc
  have hρ : partialRight (pureMatrix ψ)=ρ.matrix := density_purification_matrix ρ.toMState
  rw [hρ] at hc
  exact hc.trans hp

end ScheduleLaw.Blueprint.PhasePacketMixed
