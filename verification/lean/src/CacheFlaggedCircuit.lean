import CacheClockAdvance
import CacheFactoryBody
import CacheCellShift
import SupportPhysicalFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheFlaggedCircuit
open History

variable {k a : Type} [Fintype k] [Fintype a] [DecidableEq k] [DecidableEq a]

def level (j : k) : Mat k := pureMatrix (fun i => if i=j then 1 else 0)

def controlled (U : k → Mat a) : Mat (k × a) :=
  (blockDiagonal U).submatrix (Equiv.prodComm k a) (Equiv.prodComm k a)

theorem controlled_unitary (U : k → Mat a) (hU : ∀ j, IsUnitary (U j)) :
    IsUnitary (controlled U) :=
  unitary_submatrix _ (SupportPhysicalFrame.block_unitary U hU)

theorem sector (j : k) (ρ : Mat a) :
    level j ⊗ₖ ρ = (blockDiagonal (fun i => if i=j then ρ else 0)).submatrix
      (Equiv.prodComm k a) (Equiv.prodComm k a) := by
  ext ⟨i,u⟩ ⟨l,v⟩
  by_cases hi : i=j
  · subst i
    by_cases hl : l=j
    · subst l; simp [level,pureMatrix,blockDiagonal_apply]
    · simp [level,pureMatrix,blockDiagonal_apply,hl,Ne.symm hl]
  · by_cases hl : l=j
    · subst l; simp [level,pureMatrix,blockDiagonal_apply,hi,Ne.symm hi]
    · by_cases hil : i=l <;> simp [level,pureMatrix,blockDiagonal_apply,hi,hl,hil]

theorem controlled_sector (U : k → Mat a) (j : k) (ρ : Mat a) :
    evolve (controlled U) (level j ⊗ₖ ρ)=level j ⊗ₖ evolve (U j) ρ := by
  rw [sector,controlled,evolve_submatrix_equiv,SupportPhysicalFrame.block_evolve,sector]
  apply congrArg (fun A : k → Mat a => (blockDiagonal A).submatrix
    (Equiv.prodComm k a) (Equiv.prodComm k a))
  funext i
  by_cases hi : i=j
  · subst i; simp
  · simp [hi,evolve]

theorem kron_evolve {b : Type} [Fintype b] (U A : Mat a) (V B : Mat b) :
    evolve (U ⊗ₖ V) (A ⊗ₖ B)=evolve U A ⊗ₖ evolve V B := by
  simp only [evolve,conjTranspose_kronecker,← mul_kronecker_mul]

theorem perm_level (π : Equiv.Perm k) (j : k) :
    evolve (π.permMatrix ℂ) (level j)=level (π.symm j) := by
  rw [Recorder.permutation_evolve]
  ext i l
  have hi : π i=j ↔ i=π.symm j := π.apply_eq_iff_eq_symm_apply
  have hl : π l=j ↔ l=π.symm j := π.apply_eq_iff_eq_symm_apply
  simp [level,pureMatrix,hi,hl]

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}
abbrev Flags (n : ℕ) := CacheClockAdvance.Registers n
abbrev Physical (F : Formation β τ q (n+1)) :=
  Flags n × (CacheFactoryBody.Batch d (n+1) × CacheFactoryBody.Rest F)

def pump (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  CacheClockAdvance.pump n ⊗ₖ (1 : Mat (CacheFactoryBody.Batch d (n+1) × CacheFactoryBody.Rest F))

def factory (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  controlled (fun z : Flags n => if z.2.2=1 then CacheFactoryBody.unitary F else 1)

def rotation (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  (1 : Mat (Flags n)) ⊗ₖ
    ((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ ⊗ₖ
      (1 : Mat (CacheFactoryBody.Rest F)))

def circuit (F : Formation β τ q (n+1)) : Mat (Physical F) :=
  rotation F * factory F * pump F

def inputSector (F : Formation β τ q (n+1)) (j : Fin (n+1)) : Mat (Physical F) :=
  level (CacheClockAdvance.source n j) ⊗ₖ
    (W2.tensorFamily (CacheCellShift.sourceSector τ q n j) ⊗ₖ CacheFactoryBody.helper F)

theorem circuit_unitary (F : Formation β τ q (n+1)) : IsUnitary (circuit F) := by
  apply unitary_mul
  · apply unitary_mul
    · exact unitary_kron (by constructor <;> simp)
        (unitary_kron (Recorder.permutation_unitary _) (by constructor <;> simp))
    · apply controlled_unitary
      intro z
      split_ifs
      · exact CacheFactoryBody.unitary_ok F
      · constructor <;> simp
  · exact unitary_kron (CacheClockAdvance.pump_unitary n) (by constructor <;> simp)

theorem pump_sector (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    evolve (pump F) (inputSector F j) =
      level (CacheClockAdvance.target n j) ⊗ₖ
        (W2.tensorFamily (CacheCellShift.sourceSector τ q n j) ⊗ₖ CacheFactoryBody.helper F) := by
  rw [pump,inputSector,kron_evolve]
  change evolve ((CacheClockAdvance.permutation n).permMatrix ℂ) _ ⊗ₖ _ = _
  rw [perm_level]
  change level (CacheClockAdvance.permutation n (CacheClockAdvance.source n j)) ⊗ₖ _ = _
  rw [CacheClockAdvance.initialized_column]
  simp only [evolve,conjTranspose_one,one_mul,mul_one]

theorem boundary_input (F : Formation β τ q (n+1)) :
    W2.tensorFamily (CacheCellShift.sourceSector τ q n 0)=tensorPower q.matrix (n+1) := by
  ext u v
  simp only [W2.tensorFamily,tensorPower,CacheCellShift.sourceSector,Fin.val_zero,
    nonpos_iff_eq_zero,not_lt_zero',and_false,if_false]
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (by omega)]

theorem boundary (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    evolve (circuit F) (inputSector F 0)=
      level (CacheClockAdvance.target n 0) ⊗ₖ
        evolve ((CacheCellShift.coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ ⊗ₖ
          (1 : Mat (CacheFactoryBody.Rest F))) (CacheFactoryBody.result F) := by
  rw [circuit,evolve_mul,evolve_mul,pump_sector,factory,controlled_sector]
  simp only [CacheClockAdvance.target,if_true]
  rw [boundary_input F,CacheFactoryBody.run F hβ hq,rotation,kron_evolve]
  simp only [evolve,conjTranspose_one,one_mul,mul_one]

theorem nonboundary (F : Formation β τ q (n+1)) (j : Fin (n+1)) (hj : j≠0) :
    evolve (circuit F) (inputSector F j)=
      level (CacheClockAdvance.target n j) ⊗ₖ
        (W2.tensorFamily (fun l : Fin (n+1) => if l.val<j.val then τ else q) ⊗ₖ
          CacheFactoryBody.helper F) := by
  rw [circuit,evolve_mul,evolve_mul,pump_sector,factory,controlled_sector]
  have hid {x : Type} [Fintype x] [DecidableEq x] (A : Mat x) : evolve (1 : Mat x) A=A := by
    simp [evolve]
  simp only [CacheClockAdvance.target,if_neg hj,Fin.zero_ne_one,if_false,hid]
  rw [rotation,kron_evolve]
  simp only [hid]
  rw [kron_evolve,CacheCellShift.nonboundary_output τ q n j hj]
  simp only [hid]

end ScheduleLaw.Blueprint.CacheFlaggedCircuit
