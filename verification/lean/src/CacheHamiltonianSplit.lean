import CacheBatchSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHamiltonianSplit
open History
variable {d n : ℕ}

theorem first_condition (s t : Fin d) (u v : Fin n → Fin d) :
    (∀ l : Fin (n+1),l≠0 → (Fin.cons s u : Fin (n+1) → Fin d) l=(Fin.cons t v : Fin (n+1) → Fin d) l) ↔ u=v := by
  constructor
  · intro h
    funext l
    exact h l.succ (by simp)
  · intro h l
    refine Fin.cases ?_ ?_ l
    · intro hh; exact (hh rfl).elim
    · intro k _
      exact congrFun h k

theorem tail_condition (s t : Fin d) (u v : Fin n → Fin d) (j : Fin n) :
    (∀ l : Fin (n+1),l≠j.succ → (Fin.cons s u : Fin (n+1) → Fin d) l=(Fin.cons t v : Fin (n+1) → Fin d) l) ↔
      s=t ∧ ∀ l : Fin n,l≠j → u l=v l := by
  constructor
  · intro h
    refine ⟨h 0 (by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_zero,Fin.val_succ] at hv; omega),?_⟩
    intro l hl
    exact h l.succ (fun hh => hl (Fin.succ_inj.mp hh))
  · rintro ⟨hs,ht⟩ l
    refine Fin.cases ?_ ?_ l
    · intro _; exact hs
    · intro k hk
      exact ht k (fun h => hk (congrArg Fin.succ h))

theorem matrix (H : Mat (Fin d)) :
    (tensorHamiltonian H (n+1)).submatrix (CacheBatchSplit.split n).symm (CacheBatchSplit.split n).symm =
      H ⊗ₖ (1 : Mat (Fin n → Fin d))+(1 : Mat (Fin d)) ⊗ₖ tensorHamiltonian H n := by
  ext ⟨s,u⟩ ⟨t,v⟩
  simp only [submatrix_apply,CacheBatchSplit.split,Equiv.coe_fn_symm_mk,
    tensorHamiltonian,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,first_condition,tail_condition,
    Matrix.add_apply,kroneckerMap_apply,Matrix.one_apply]
  by_cases hst : s=t <;> simp [hst]

end ScheduleLaw.Blueprint.CacheHamiltonianSplit
