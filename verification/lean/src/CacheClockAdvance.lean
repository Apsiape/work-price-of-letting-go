import FiniteSwap
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder
namespace ScheduleLaw.Blueprint.CacheClockAdvance

def step (n : ℕ) : Equiv.Perm (Fin (n+1)) := (finRotate (n+1)).symm

def clockEnergy (n : ℕ) (a : ℝ) (k : Fin (n+1)) : ℝ := ((n-k.val : ℕ) : ℝ)*a

theorem step_zero (n : ℕ) : step n 0=Fin.last n :=
  (finRotate (n+1)).symm_apply_eq.mpr finRotate_last.symm

theorem clock_change (n : ℕ) (a : ℝ) (k : Fin (n+1)) :
    clockEnergy n a (step n k)-clockEnergy n a k =
      a-(if k=0 then (n+1 : ℝ)*a else 0) := by
  by_cases hk : k=0
  · subst k
    rw [step_zero]
    simp only [clockEnergy,Fin.val_last,Fin.val_zero,Nat.sub_self,Nat.cast_zero,
      zero_mul,Nat.sub_zero,if_true,Nat.cast_add,Nat.cast_one]
    ring
  · have hs : (step n k).val=k.val-1 := coe_finRotate_symm_of_ne_zero hk
    have hval : k.val≠0 := Fin.val_ne_zero_iff.mpr hk
    have hN : n-(k.val-1)=(n-k.val)+1 := by have := k.isLt; omega
    change ((n-(step n k).val : ℕ) : ℝ)*a-((n-k.val : ℕ) : ℝ)*a = _
    rw [hs,hN,Nat.cast_add,Nat.cast_one,if_neg hk]
    ring

abbrev Registers (n : ℕ) := Fin (n+1) × (Fin 2 × Fin 2)

def source (n : ℕ) (k : Fin (n+1)) : Registers n := (k,0,0)
def target (n : ℕ) (k : Fin (n+1)) : Registers n := (step n k,1,if k=0 then 1 else 0)

theorem source_injective (n : ℕ) : Function.Injective (source n) := by
  intro i j h
  exact congrArg Prod.fst h

theorem target_injective (n : ℕ) : Function.Injective (target n) := by
  intro i j h
  exact (step n).injective (congrArg Prod.fst h)

theorem disjoint (n : ℕ) (i j : Fin (n+1)) : source n i≠target n j := by
  intro h
  have hw := congrArg (fun z : Registers n => z.2.1) h
  exact Fin.zero_ne_one hw

def permutation (n : ℕ) : Equiv.Perm (Registers n) :=
  FiniteSwap.permutation (source n) (target n) (source_injective n) (target_injective n) (disjoint n)

/-- Complete square clock/main/auxiliary pump. The same main debit is
used on all sectors; only the boundary receives the m-copy factory credit. -/
def pump (n : ℕ) : Mat (Registers n) := (permutation n).permMatrix ℂ

theorem pump_unitary (n : ℕ) : IsUnitary (pump n) := Recorder.permutation_unitary _

theorem initialized_column (n : ℕ) (k : Fin (n+1)) :
    permutation n (source n k)=target n k :=
  FiniteSwap.on_source (source n) (target n) (source_injective n) k

def energy (n : ℕ) (a : ℝ) (z : Registers n) : ℝ :=
  clockEnergy n a z.1+(if z.2.1=1 then -a else 0)+
    (if z.2.2=1 then (n+1 : ℝ)*a else 0)

theorem column_energy (n : ℕ) (a : ℝ) (k : Fin (n+1)) :
    energy n a (target n k)=energy n a (source n k) := by
  have h := clock_change n a k
  by_cases hk : k=0 <;> simp [energy,source,target,hk] at * <;> linarith

theorem pump_conserves (n : ℕ) (a : ℝ) :
    Conserves (pump n) (diagonal (fun z => (energy n a z : ℂ))) :=
  FiniteSwap.conserves (source n) (target n) (source_injective n) (target_injective n)
    (disjoint n) (energy n a) (column_energy n a)

end ScheduleLaw.Blueprint.CacheClockAdvance

