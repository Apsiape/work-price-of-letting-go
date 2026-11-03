import SupportPhysicalFrame
import SupportRun

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

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq c] in
theorem blocks_add (A D : b → Mat a) (B : Mat c) :
    blocks (fun j => A j+D j) B = blocks A B+blocks D B := by
  change blocks (A+D) B = _
  simp only [blocks,blockDiagonal_add,add_kronecker,submatrix_add,Pi.add_apply]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq c] in
theorem blocks_const (A : Mat a) (B : Mat c) :
    blocks (fun _ : b => A) B = A ⊗ₖ ((1 : Mat b) ⊗ₖ B) := by
  ext ⟨i,⟨w,k⟩⟩ ⟨j,⟨v,h⟩⟩
  simp only [blocks,submatrix_apply,Equiv.prodAssoc_symm_apply,blockDiagonal_apply,
    kroneckerMap_apply,one_apply]
  split_ifs <;> simp

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq c] in
theorem blocks_scalar (x : b → ℂ) (B : Mat c) :
    blocks (fun j => x j • (1 : Mat a)) B =
      (1 : Mat a) ⊗ₖ ((diagonal x) ⊗ₖ B) := by
  ext ⟨i,⟨w,k⟩⟩ ⟨j,⟨v,h⟩⟩
  simp only [blocks,submatrix_apply,Equiv.prodAssoc_symm_apply,blockDiagonal_apply,
    kroneckerMap_apply,one_apply,smul_apply,smul_eq_mul,Matrix.diagonal]
  split_ifs <;> simp_all

omit [Fintype a] [Fintype b] [Fintype c] in
theorem blocks_diagonal (E : b → a → ℂ) (R : c → ℂ) :
    blocks (fun j => diagonal (E j)) (diagonal R) =
      diagonal (fun z => E z.2.1 z.1 * R z.2.2) := by
  unfold blocks
  rw [blockDiagonal_diagonal,diagonal_kronecker_diagonal,submatrix_diagonal_equiv]
  rfl

omit [Fintype a] [Fintype b] [Fintype c] in
theorem blocks_sum_diagonal (E : b → a → ℂ) (R : c → ℂ) :
    blocks (fun j => diagonal (E j)) (1 : Mat c) +
      blocks (fun _ : b => (1 : Mat a)) (diagonal R) =
      diagonal (fun z => E z.2.1 z.1 + R z.2.2) := by
  have h1 : (1 : Mat c)=diagonal (fun _ => (1 : ℂ)) := rfl
  have h2 : (fun _ : b => (1 : Mat a))=(fun _ : b => diagonal (fun _ : a => (1 : ℂ))) := rfl
  rw [h1,h2,blocks_diagonal,blocks_diagonal,diagonal_add]
  simp only [mul_one,one_mul]

omit [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq c] in
theorem blocks_level (A : Mat a) (B : Mat c) (k : Fin 2) :
    blocks (fun j : Fin 2 => if j=k then A else 0) B =
      A ⊗ₖ (SupportRun.level k ⊗ₖ B) := by
  rw [SupportRun.level_diagonal]
  ext ⟨i,⟨w,t⟩⟩ ⟨j,⟨v,h⟩⟩
  simp only [blocks,submatrix_apply,Equiv.prodAssoc_symm_apply,blockDiagonal_apply,
    kroneckerMap_apply,Matrix.of_apply,Matrix.diagonal]
  split_ifs <;> simp_all

theorem frame_hamiltonian (U : b → Mat a) (hU : ∀ j, IsUnitary (U j))
    (H : Mat a) (E : b → a → ℝ) (R : c → ℝ) (x : b → ℝ)
    (hH : ∀ j, evolve (U j) (diagonal (fun i => (E j i : ℂ)))=H) :
    evolve (frame (c:=c) U)
      (diagonal (fun z => ((E z.2.1 z.1+x z.2.1+R z.2.2 : ℝ) : ℂ))) =
      H ⊗ₖ (1 : Mat (b × c)) + (1 : Mat a) ⊗ₖ
        ((diagonal (fun j => (x j : ℂ))) ⊗ₖ (1 : Mat c) +
          (1 : Mat b) ⊗ₖ (diagonal (fun k => (R k : ℂ)))) := by
  have he : diagonal (fun z : a × (b × c) => ((E z.2.1 z.1+x z.2.1+R z.2.2 : ℝ) : ℂ)) =
      blocks (fun j => diagonal (fun i => ((E j i+x j : ℝ) : ℂ))) (1 : Mat c)+
        blocks (fun _ : b => (1 : Mat a)) (diagonal (fun k => (R k : ℂ))) := by
    rw [blocks_sum_diagonal]
    simp only [Complex.ofReal_add]
  rw [he]
  have hadd (W A B : Mat (a × (b × c))) : evolve W (A+B)=evolve W A+evolve W B := by
    simp only [evolve,mul_add,add_mul]
  rw [hadd,frame_evolve,frame_one U hU]
  have hf : (fun j => evolve (U j) (diagonal (fun i => ((E j i+x j : ℝ) : ℂ)))) =
      (fun j => H+(x j : ℂ) • (1 : Mat a)) := by
    funext j
    have hd : diagonal (fun i : a => ((E j i+x j : ℝ) : ℂ)) =
        diagonal (fun i => (E j i : ℂ))+(x j : ℂ) • (1 : Mat a) := by
      ext i k
      by_cases hi : i=k <;> simp [Matrix.diagonal,hi,Complex.ofReal_add]
    rw [hd]
    simp only [evolve,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,
      (hU j).2]
    exact congrArg (fun A => A+(x j : ℂ) • (1 : Mat a)) (hH j)
  rw [hf,blocks_add,blocks_const,blocks_scalar,blocks_const]
  rw [one_kronecker_one,kronecker_add]
  simp only [add_assoc]

end ScheduleLaw.Blueprint.SupportPhysicalFrame
