import WireTensor

/-! The arrival routing identity for rectangular open-device kernels.
The carrier slot is distinct from its visit-indexed stored input/partner. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

abbrev PortStock (s c : Type) := s × (c × c)
abbrev PortInput (s h c u : Type) := (PortStock s c × h) × (c × u)
abbrev PortOutput (b h c u : Type) := (b × h) × (c × u)
abbrev PortRest (s h c u : Type) := ((s × c) × h) × u

def arrivalExchange {s h c u : Type} (x : PortInput s h c u) : PortInput s h c u :=
  (((x.1.1.1,(x.2.1,x.1.1.2.2)),x.1.2),(x.1.1.2.1,x.2.2))

theorem arrivalExchange_involutive {s h c u : Type} :
    Function.Involutive (arrivalExchange (s := s) (h := h) (c := c) (u := u)) := by
  rintro ⟨⟨⟨s,a,o⟩,h⟩,p,u⟩
  rfl

def arrivalPermutation (s h c u : Type) : Equiv.Perm (PortInput s h c u) :=
  arrivalExchange_involutive.toPerm

theorem arrivalPermutation_symm (s h c u : Type) :
    (arrivalPermutation s h c u).symm = arrivalPermutation s h c u := rfl

def unheldLift {b s h c u : Type} [DecidableEq c] [DecidableEq u]
    (K : Matrix (b × h) (PortStock s c × h) ℂ) :
    Matrix (PortOutput b h c u) (PortInput s h c u) ℂ := K ⊗ₖ (1 : Mat (c × u))

def heldLift {b s h c u : Type} [DecidableEq u]
    (K : Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ) :
    Matrix (PortOutput b h c u) (PortInput s h c u) ℂ :=
  (K ⊗ₖ (1 : Mat u)).submatrix (Equiv.prodAssoc (b × h) c u).symm
    (Equiv.prodAssoc (PortStock s c × h) c u).symm

def arrivalKernel {b s h c : Type} [DecidableEq c]
    (K : Matrix (b × h) (PortStock s c × h) ℂ) :
    Matrix ((b × h) × c) ((PortStock s c × h) × c) ℂ := fun i j =>
  K i.1 ((j.1.1.1,(j.2,j.1.1.2.2)),j.1.2) * if i.2 = j.1.1.2.1 then 1 else 0

theorem arrival_kernel_routing {b s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (K : Matrix (b × h) (PortStock s c × h) ℂ) :
    heldLift (u := u) (arrivalKernel K) =
      unheldLift (u := u) K * (arrivalPermutation s h c u).permMatrix ℂ := by
  ext i j
  rw [mul_permutation_entry,arrivalPermutation_symm]
  change K i.1 ((j.1.1.1,(j.2.1,j.1.1.2.2)),j.1.2) *
    (if i.2.1 = j.1.1.2.1 then 1 else 0) * (if i.2.2 = j.2.2 then 1 else 0) =
      K i.1 ((j.1.1.1,(j.2.1,j.1.1.2.2)),j.1.2) *
        (if i.2 = (j.1.1.2.1,j.2.2) then 1 else 0)
  by_cases hc : i.2.1 = j.1.1.2.1 <;> by_cases hu : i.2.2 = j.2.2 <;> simp [Prod.ext_iff,hc,hu]

def freshCoordinates (s h c u : Type) : PortInput s h c u ≃ (c × c) × PortRest s h c u where
  toFun x := ((x.1.1.2.2,x.2.1),(((x.1.1.1,x.1.1.2.1),x.1.2),x.2.2))
  invFun x := (((x.2.1.1.1,(x.2.1.1.2,x.1.1)),x.2.1.2),(x.1.2,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def freshInsertion (s h c u : Type) [Fintype c] [DecidableEq c]
    [DecidableEq s] [DecidableEq h] [DecidableEq u] :
    Matrix (PortInput s h c u) (PortRest s h c u) ℂ :=
  (ketInsert (z := PortRest s h c u) (Recorder.epr (a := c))).submatrix (freshCoordinates s h c u) id

theorem freshInsertion_state {s h c u : Type} [Fintype s] [Fintype h] [Fintype c]
    [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (ρ : Mat (PortRest s h c u)) :
    freshInsertion s h c u * ρ * (freshInsertion s h c u)ᴴ =
      ((pureMatrix (Recorder.epr (a := c))) ⊗ₖ ρ).submatrix
        (freshCoordinates s h c u) (freshCoordinates s h c u) := by
  have he := ketInsert_sandwich (Recorder.epr (a := c)) ρ
  have ht := congrArg (fun A => A.submatrix (freshCoordinates s h c u) (freshCoordinates s h c u)) he
  simpa only [freshInsertion,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id] using ht

theorem kernel_freshInsertion_entry {b s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (L : Matrix b (PortInput s h c u) ℂ) (i : b) (z : PortRest s h c u) :
    (L * freshInsertion s h c u) i z =
      ∑ p : c × c, L i ((freshCoordinates s h c u).symm (p,z)) * Recorder.epr p := by
  rw [Matrix.mul_apply,← Equiv.sum_comp (freshCoordinates s h c u).symm
    (fun x => L i x * freshInsertion s h c u x z),Fintype.sum_prod_type]
  simp [freshInsertion,ketInsert,mul_ite,ite_mul,Finset.sum_ite_irrel]

end ScheduleLaw.History.Wire
