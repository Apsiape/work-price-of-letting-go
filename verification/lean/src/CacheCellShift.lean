import FactoryTensorHamiltonian
import FactoryPermutation
import W2.TensorFamily
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheCellShift
open History

def coordinates {ι a : Type} (p : Equiv.Perm ι) : Equiv.Perm (ι → a) where
  toFun u k := u (p k)
  invFun u k := u (p.symm k)
  left_inv u := by funext k; simp only [Equiv.apply_symm_apply]
  right_inv u := by funext k; simp only [Equiv.symm_apply_apply]

theorem tensor_state {ι a : Type} [Fintype ι] [Fintype a] [DecidableEq ι] [DecidableEq a]
    (p : Equiv.Perm ι) (ρ : ι → Density a) :
    evolve ((coordinates (a:=a) p).permMatrix ℂ) (W2.tensorFamily ρ)=
      W2.tensorFamily (fun k => ρ (p.symm k)) := by
  rw [Recorder.permutation_evolve]
  ext u v
  have he := Equiv.prod_comp p (fun k => (ρ (p.symm k)).matrix (u k) (v k))
  simpa only [W2.tensorFamily,submatrix_apply,coordinates,Equiv.coe_fn_mk,
    Equiv.symm_apply_apply] using he

theorem tensor_hamiltonian {d m : ℕ} (p : Equiv.Perm (Fin m)) (H : Mat (Fin d)) :
    (tensorHamiltonian H m).submatrix (coordinates p) (coordinates p)=tensorHamiltonian H m := by
  ext u v
  have hcond (k : Fin m) :
      (∀ l, l≠k → u (p l)=v (p l)) ↔ (∀ l, l≠p k → u l=v l) := by
    constructor
    · intro h l hl
      obtain ⟨r,rfl⟩ := p.surjective l
      exact h r (fun hr => hl (congrArg p hr))
    · intro h l hl
      exact h (p l) (p.injective.ne hl)
  have he := Equiv.sum_comp p (fun k => H (u k) (v k)*
    if ∀ l, l≠k → u l=v l then (1 : ℂ) else 0)
  simpa only [tensorHamiltonian,submatrix_apply,coordinates,Equiv.coe_fn_mk,hcond] using he

theorem conserving {d m : ℕ} (p : Equiv.Perm (Fin m)) (H : Mat (Fin d)) :
    Conserves ((coordinates (a:=Fin d) p).permMatrix ℂ) (tensorHamiltonian H m) := by
  let π := coordinates (a:=Fin d) p
  have h := Recorder.permutation_evolve π.symm (tensorHamiltonian H m)
  have hp : π.symm=coordinates p.symm := rfl
  rw [evolve,conjTranspose_permMatrix] at h
  unfold Conserves
  rw [conjTranspose_permMatrix]
  exact h.trans (by rw [hp,tensor_hamiltonian])

def sourceSector {a : Type} [Fintype a] (τ q : Density a) (n : ℕ)
    (k j : Fin (n+1)) : Density a := if 0<j.val ∧ j.val≤k.val then τ else q

theorem nonboundary_sector {a : Type} [Fintype a] (τ q : Density a) (n : ℕ)
    (k : Fin (n+1)) (hk : k≠0) (j : Fin (n+1)) :
    sourceSector τ q n k (finRotate (n+1) j) = if j.val<k.val then τ else q := by
  have hk0 : k.val≠0 := Fin.val_ne_zero_iff.mpr hk
  by_cases hj : j=Fin.last n
  · subst j
    simp only [sourceSector,finRotate_last,Fin.val_zero,lt_self_iff_false,false_and,if_false,Fin.val_last]
    rw [if_neg (by have := k.isLt; omega)]
  · have hrot := coe_finRotate_of_ne_last hj
    unfold sourceSector
    rw [hrot]
    have hc : (0<j.val+1 ∧ j.val+1≤k.val) ↔ j.val<k.val := by omega
    simp only [hc]

theorem nonboundary_output {d : ℕ} (τ q : Density (Fin d)) (n : ℕ)
    (k : Fin (n+1)) (hk : k≠0) :
    evolve ((coordinates (a:=Fin d) (finRotate (n+1)).symm).permMatrix ℂ)
      (W2.tensorFamily (sourceSector τ q n k)) =
      W2.tensorFamily (fun j : Fin (n+1) => if j.val<k.val then τ else q) := by
  rw [tensor_state]
  apply congrArg W2.tensorFamily
  funext j
  simpa only [Equiv.symm_symm] using nonboundary_sector τ q n k hk j

end ScheduleLaw.Blueprint.CacheCellShift
