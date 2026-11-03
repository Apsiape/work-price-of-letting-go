import EndpointKernel

/-! Release bends the current carrier action onto its retained partner.
The identity holds for arbitrary rest/reference matrices and for two
different device kernels; no inverse or loss of dilation waste occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

def releaseKernel {b s h c : Type} [Fintype c]
    (K : Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ) :
    Matrix (b × h) (PortStock s c × h) ℂ := fun i j =>
  ∑ y : c, K (i,j.1.2.2) (((j.1.1,(j.1.2.1,y)),j.2),y)

theorem held_kernel_cup_entry {b s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (K : Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ)
    (i : PortOutput b h c u) (z : PortRest s h c u) :
    (heldLift (u := u) K * freshInsertion s h c u) i z =
      (∑ y : c, K (i.1,i.2.1) (((z.1.1.1,(z.1.1.2,y)),z.1.2),y)) *
        ((Real.sqrt (Fintype.card c))⁻¹ : ℝ) * if i.2.2 = z.2 then 1 else 0 := by
  rw [kernel_freshInsertion_entry]
  change (∑ p : c × c, K (i.1,i.2.1) (((z.1.1.1,(z.1.1.2,p.1)),z.1.2),p.2) *
    (1 : Mat u) i.2.2 z.2 * Recorder.epr p) = _
  rw [Fintype.sum_prod_type]
  by_cases hu : i.2.2 = z.2 <;> simp [Recorder.epr,one_apply,hu,Finset.sum_mul]

theorem released_kernel_cup_entry {b s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (K : Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ)
    (i : PortOutput b h c u) (z : PortRest s h c u) :
    (unheldLift (u := u) (releaseKernel K) * freshInsertion s h c u) i z =
      (∑ y : c, K (i.1,i.2.1) (((z.1.1.1,(z.1.1.2,y)),z.1.2),y)) *
        ((Real.sqrt (Fintype.card c))⁻¹ : ℝ) * if i.2.2 = z.2 then 1 else 0 := by
  rw [kernel_freshInsertion_entry]
  change (∑ p : c × c, releaseKernel K i.1 ((z.1.1.1,(z.1.1.2,p.1)),z.1.2) *
    (1 : Mat (c × u)) i.2 (p.2,z.2) * Recorder.epr p) = _
  rw [Fintype.sum_prod_type]
  by_cases hu : i.2.2 = z.2 <;>
    simp [Recorder.epr,one_apply,Prod.ext_iff,hu,releaseKernel,Finset.sum_mul,eq_comm]

theorem release_kernel_routing {b s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (K : Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ) :
    heldLift (u := u) K * freshInsertion s h c u =
      unheldLift (u := u) (releaseKernel K) * freshInsertion s h c u := by
  ext i z
  rw [held_kernel_cup_entry,released_kernel_cup_entry]

theorem release_cross_state {b d s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (K : Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ)
    (L : Matrix ((d × h) × c) ((PortStock s c × h) × c) ℂ)
    (ρ : Mat (PortRest s h c u)) :
    heldLift (u := u) K * (((pureMatrix (Recorder.epr (a := c))) ⊗ₖ ρ).submatrix
      (freshCoordinates s h c u) (freshCoordinates s h c u)) * (heldLift (u := u) L)ᴴ =
    unheldLift (u := u) (releaseKernel K) * (((pureMatrix (Recorder.epr (a := c))) ⊗ₖ ρ).submatrix
      (freshCoordinates s h c u) (freshCoordinates s h c u)) * (unheldLift (u := u) (releaseKernel L))ᴴ := by
  rw [← freshInsertion_state]
  exact cross_sandwich_eq_of_insert_eq _ _ _ _ _ (release_kernel_routing (u := u) K)
    (release_kernel_routing (u := u) L) ρ

end ScheduleLaw.History.Wire
