import SupportTiledGate
import SupportCoordinates
import FlatTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportPhysicalFrame
open History

variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

theorem block_unitary (U : b → Mat a) (hU : ∀ j, IsUnitary (U j)) :
    IsUnitary (blockDiagonal U) := by
  constructor
  · rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [(hU _).1]
    exact blockDiagonal_one
  · rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [(hU _).2]
    exact blockDiagonal_one

omit [DecidableEq a] in
theorem block_evolve (U A : b → Mat a) :
    evolve (blockDiagonal U) (blockDiagonal A) =
      blockDiagonal (fun j => evolve (U j) (A j)) := by
  simp only [evolve,blockDiagonal_conjTranspose,← blockDiagonal_mul]

def frame (U : b → Mat a) : Mat (a × (b × c)) :=
  ((blockDiagonal U) ⊗ₖ (1 : Mat c)).submatrix
    (Equiv.prodAssoc a b c).symm (Equiv.prodAssoc a b c).symm

theorem frame_unitary (U : b → Mat a) (hU : ∀ j, IsUnitary (U j)) :
    IsUnitary (frame (c:=c) U) := by
  exact unitary_submatrix _ (unitary_kron (block_unitary U hU)
    (by constructor <;> simp))

def blocks (A : b → Mat a) (B : Mat c) : Mat (a × (b × c)) :=
  ((blockDiagonal A) ⊗ₖ B).submatrix
    (Equiv.prodAssoc a b c).symm (Equiv.prodAssoc a b c).symm

theorem frame_evolve (U A : b → Mat a) (B : Mat c) :
    evolve (frame U) (blocks A B) = blocks (fun j => evolve (U j) (A j)) B := by
  unfold frame blocks
  rw [evolve_submatrix_equiv]
  congr 1
  simp only [evolve,conjTranspose_kronecker,conjTranspose_one,
    ← mul_kronecker_mul,one_mul,mul_one,blockDiagonal_conjTranspose,
    ← blockDiagonal_mul]

theorem frame_one (U : b → Mat a) (hU : ∀ j, IsUnitary (U j)) (B : Mat c) :
    evolve (frame U) (blocks (fun _ : b => (1 : Mat a)) B) =
      blocks (fun _ : b => (1 : Mat a)) B := by
  rw [frame_evolve]
  congr 1
  funext j
  simp only [evolve,mul_one,(hU j).2]

theorem conjugate_conserves (W U H : Mat a) (hW : IsUnitary W)
    (hU : Conserves U H) : Conserves (W*U*Wᴴ) (evolve W H) := by
  unfold Conserves evolve at *
  simp only [conjTranspose_mul,conjTranspose_conjTranspose,mul_assoc]
  simp only [← mul_assoc Wᴴ W,hW.1,one_mul]
  simpa only [mul_assoc] using congrArg (fun A => W*A*Wᴴ) hU

theorem conjugate_effect (W U Q P : Mat a) (hW : IsUnitary W)
    (hgap : (Uᴴ*Q*U-P).PosSemidef) :
    ((W*U*Wᴴ)ᴴ*(evolve W Q)*(W*U*Wᴴ)-evolve W P).PosSemidef := by
  have h := hgap.mul_mul_conjTranspose_same W
  convert h using 1
  simp only [evolve,conjTranspose_mul,conjTranspose_conjTranspose,mul_sub,sub_mul,
    mul_assoc]
  simp only [← mul_assoc Wᴴ W,hW.1,one_mul]

end ScheduleLaw.Blueprint.SupportPhysicalFrame
