import PhaseShellBlocks
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder
namespace ScheduleLaw.Blueprint.FinitePhaseShell

variable {ι G : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup G] [DecidableEq G]

abbrev State (B : Finset G) := ι × ↥B

def shells (a : ι → G) (B : Finset G) : Finset G :=
  Finset.univ.image (fun x : State (ι:=ι) B => x.2.val+a x.1)

abbrev Shell (a : ι → G) (B : Finset G) := ↥(shells a B)

def tag (a : ι → G) (B : Finset G) (x : State (ι:=ι) B) : Shell a B :=
  ⟨x.2.val+a x.1,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩

abbrev Fiber (a : ι → G) (B : Finset G) (t : Shell a B) :=
  {x : State (ι:=ι) B // tag a B x=t}

def Complete (a : ι → G) (B : Finset G) (t : Shell a B) : Prop :=
  ∀ i, t.val-a i ∈ B

def fiberEquiv (a : ι → G) (B : Finset G) (t : Shell a B) (ht : Complete a B t) :
    Fiber a B t ≃ ι where
  toFun x := x.val.1
  invFun i := ⟨(i,⟨t.val-a i,ht i⟩),by
    apply Subtype.ext
    change (t.val-a i)+a i=t.val
    abel⟩
  left_inv x := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply Subtype.ext
    have hx := congrArg Subtype.val x.property
    change x.val.2.val+a x.val.1=t.val at hx
    change t.val-a x.val.1=x.val.2.val
    rw [← hx]
    abel
  right_inv _ := rfl

def block (a : ι → G) (B : Finset G) (U : Mat ι) (t : Shell a B) : Mat (Fiber a B t) :=
  if ht : Complete a B t then U.submatrix (fiberEquiv a B t ht) (fiberEquiv a B t ht) else 1

def frame (a : ι → G) (B : Finset G) : State (ι:=ι) B ≃ Sigma (Fiber a B) :=
  (Equiv.sigmaFiberEquiv (tag a B)).symm

def gate (a : ι → G) (B : Finset G) (U : Mat ι) : Mat (State (ι:=ι) B) :=
  (blockDiagonal' (block a B U)).submatrix (frame a B) (frame a B)

theorem block_unitary (a : ι → G) (B : Finset G) (U : Mat ι) (hU : IsUnitary U)
    (t : Shell a B) : IsUnitary (block a B U t) := by
  unfold block
  split_ifs with ht
  · exact unitary_submatrix (fiberEquiv a B t ht) hU
  · constructor <;> simp

theorem unitary (a : ι → G) (B : Finset G) (U : Mat ι) (hU : IsUnitary U) :
    IsUnitary (gate a B U) :=
  unitary_submatrix (frame a B) (PhaseShellBlocks.block_unitary _ (block_unitary a B U hU))

/-- A finite full-square gate conserves the literal additive total energy;
no rational commensurability of the real energies is assumed. -/
theorem conserving (a : ι → G) (B : Finset G) (ω : G →+ ℝ) (U : Mat ι) (hU : IsUnitary U) :
    Conserves (gate a B U) (diagonal (fun x : State (ι:=ι) B => ((ω (a x.1)+ω x.2.val : ℝ) : ℂ))) := by
  have hh := (PhaseShellBlocks.transport (frame a B) (block a B U)
    (block_unitary a B U hU) (fun t => ω t.val)).2
  have hH : (diagonal (fun x : Sigma (Fiber a B) => (ω x.1.val : ℂ))).submatrix
      (frame a B) (frame a B) =
        diagonal (fun x : State (ι:=ι) B => ((ω (a x.1)+ω x.2.val : ℝ) : ℂ)) := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    change (ω (x.2.val+a x.1) : ℂ)=((ω (a x.1)+ω x.2.val : ℝ) : ℂ)
    rw [map_add,add_comm]
  rw [hH] at hh
  exact hh

theorem frame_fiber (a : ι → G) (B : Finset G) (t : Shell a B) (x : Fiber a B t) :
    frame a B x.val=⟨t,x⟩ := by
  apply (Equiv.sigmaFiberEquiv (tag a B)).injective
  rfl

theorem complete_action (a : ι → G) (B : Finset G) (U : Mat ι) (t : Shell a B)
    (ht : Complete a B t) (x y : Fiber a B t) : gate a B U x.val y.val=U x.val.1 y.val.1 := by
  simp only [gate,submatrix_apply,frame_fiber,blockDiagonal'_apply_eq,block,dif_pos ht,
    fiberEquiv,Equiv.coe_fn_mk]

end ScheduleLaw.Blueprint.FinitePhaseShell
