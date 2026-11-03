import CacheFlaggedCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheBatchSplit
open History

variable {a : Type} [Fintype a] [DecidableEq a]

def split (n : ℕ) : (Fin (n+1) → a) ≃ a × (Fin n → a) where
  toFun u := (u 0,fun j => u j.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv u := by funext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

theorem tensor (n : ℕ) (ρ : Fin (n+1) → Density a) :
    (W2.tensorFamily ρ).submatrix (split n).symm (split n).symm =
      (ρ 0).matrix ⊗ₖ W2.tensorFamily (fun j : Fin n => ρ j.succ) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [submatrix_apply,W2.tensorFamily,split,Equiv.coe_fn_symm_mk,
    Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,kroneckerMap_apply]

def cacheSector (τ q : Density a) (n : ℕ) (j : Fin (n+1)) : Density (Fin n → a) :=
  W2.tensorFamilyDensity (fun l => if l.val<j.val then τ else q)

theorem source (τ q : Density a) (n : ℕ) (j : Fin (n+1)) :
    (W2.tensorFamily (CacheCellShift.sourceSector τ q n j)).submatrix
      (split n).symm (split n).symm = q.matrix ⊗ₖ (cacheSector τ q n j).matrix := by
  rw [tensor]
  have h0 : CacheCellShift.sourceSector τ q n j 0=q := by simp [CacheCellShift.sourceSector]
  rw [h0]
  congr 1
  apply congrArg W2.tensorFamily
  funext l
  unfold CacheCellShift.sourceSector
  have hc : (0<l.succ.val ∧ l.succ.val≤j.val) ↔ l.val<j.val := by simp only [Fin.val_succ]; omega
  simp only [hc]

theorem emitted (τ q : Density a) (n : ℕ) (j : Fin (n+1)) (hj : j≠0) :
    (W2.tensorFamily (fun l : Fin (n+1) => if l.val<j.val then τ else q)).submatrix
      (split n).symm (split n).symm =
      τ.matrix ⊗ₖ (cacheSector τ q n (CacheClockAdvance.step n j)).matrix := by
  rw [tensor]
  have hj0 : 0<j.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hj)
  simp only [Fin.val_zero,hj0,if_true]
  congr 1
  apply congrArg W2.tensorFamily
  funext l
  have hs := coe_finRotate_symm_of_ne_zero hj
  change (if l.succ.val<j.val then τ else q)=
    (if l.val<(CacheClockAdvance.step n j).val then τ else q)
  change (CacheClockAdvance.step n j).val=j.val-1 at hs
  rw [hs]
  have hc : l.succ.val<j.val ↔ l.val<j.val-1 := by simp only [Fin.val_succ]; omega
  simp only [hc]

theorem level_prod {b : Type} [Fintype b] [DecidableEq b] (i : a) (j : b) :
    CacheFlaggedCircuit.level (i,j)=CacheFlaggedCircuit.level i ⊗ₖ CacheFlaggedCircuit.level j := by
  ext ⟨u,v⟩ ⟨u',v'⟩
  by_cases h1 : u=i <;> by_cases h2 : u'=i <;>
    by_cases h3 : v=j <;> by_cases h4 : v'=j <;>
    simp [CacheFlaggedCircuit.level,pureMatrix,h1,h2,h3,h4]

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def frame (F : Formation β τ q (n+1)) : CacheFlaggedCircuit.Physical F ≃
    (Fin (n+1) × (Fin n → Fin d)) ×
      ((Fin 2 × Fin 2) × (Fin d × CacheFactoryBody.Rest F)) where
  toFun | ((j,w,v),batch,rest) => ((j,(split n batch).2),(w,v),(split n batch).1,rest)
  invFun | ((j,cache),(w,v),b,rest) => ((j,w,v),(split n).symm (b,cache),rest)
  left_inv z := by rcases z with ⟨⟨j,w,v⟩,batch,rest⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨j,cache⟩,⟨w,v⟩,b,rest⟩; simp only [Equiv.apply_symm_apply]

theorem input_sector (F : Formation β τ q (n+1)) (j : Fin (n+1)) :
    (CacheFlaggedCircuit.inputSector F j).submatrix (frame F).symm (frame F).symm =
      (CacheFlaggedCircuit.level j ⊗ₖ (cacheSector τ q n j).matrix) ⊗ₖ
        (CacheFlaggedCircuit.level ((0 : Fin 2),(0 : Fin 2)) ⊗ₖ
          (q.matrix ⊗ₖ CacheFactoryBody.helper F)) := by
  ext ⟨⟨k,u⟩,⟨w,v⟩,b,r⟩ ⟨⟨k',u'⟩,⟨w',v'⟩,b',r'⟩
  have ht := congrFun (congrFun (source τ q n j) (b,u)) (b',u')
  simp only [submatrix_apply,kroneckerMap_apply] at ht
  have hf := congrArg (fun M : Mat (Fin (n+1) × (Fin 2 × Fin 2)) =>
    M (k,w,v) (k',w',v')) (level_prod j ((0 : Fin 2),(0 : Fin 2)))
  simp only [kroneckerMap_apply] at hf
  simp only [CacheFlaggedCircuit.inputSector,submatrix_apply,frame,Equiv.coe_fn_symm_mk,
    kroneckerMap_apply]
  change CacheFlaggedCircuit.level (j,0,0) (k,w,v) (k',w',v') *
    (W2.tensorFamily (CacheCellShift.sourceSector τ q n j)
      ((split n).symm (b,u)) ((split n).symm (b',u')) * CacheFactoryBody.helper F r r') = _
  rw [hf,ht]
  ring

end ScheduleLaw.Blueprint.CacheBatchSplit
