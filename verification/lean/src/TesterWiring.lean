import RecorderSchedule
import PurifiedScore

/-! Coherent tester amplitudes from explicit time-wire routing. The recurrence
uses tester matrices and visit SWAPs, independently of run and jointGate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

abbrev Raw {I : Inventory} (S : Schedule I) (r : ℕ) :=
  Recorder.Stock S × (Payload I × Fin r)

def actual {I : Inventory} (S : Schedule I) (r : ℕ) :
    Raw S r ≃ Global (Recorder.extension S) r :=
  Equiv.prodCongr (Recorder.stockFin S) (Equiv.refl _)

def wire {I : Inventory} {S : Schedule I} (k : Cut S) (r : ℕ) : Equiv.Perm (Raw S r) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodCongr (Recorder.contact k) (Equiv.refl (Fin r))).trans
      (Equiv.prodAssoc _ _ _))

theorem wire_apply {I : Inventory} {S : Schedule I} (k : Cut S) (r : ℕ) (x : Raw S r) :
    wire k r x = ((Recorder.contact k (x.1,x.2.1)).1,
      ((Recorder.contact k (x.1,x.2.1)).2,x.2.2)) := rfl

def step {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (k : Cut S)
    (v : Raw S r → ℂ) : Raw S r → ℂ :=
  fun x => ∑ z : Payload I × Fin r,
    t.gate k (x.2.2,x.2.1) (z.2,z.1) * v (wire k r (x.1,z))

def amplitudes {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (φ : Recorder.Stock S → ℂ) : ℕ → Raw S r → ℂ
  | 0 => fun x => φ x.1 * t.initial (x.2.2,x.2.1)
  | n+1 => if h : n < 2*S.visits+1 then step t ⟨n,h⟩ (amplitudes t φ n)
      else amplitudes t φ n

theorem device_raw {I : Inventory} (S : Schedule I) (r : ℕ) (k : Cut S) :
    (liftDeviceObservable (Recorder.extension S) r ((Recorder.extension S).gate k)).submatrix
      (actual S r) (actual S r) = (wire k r).permMatrix ℂ := by
  ext i j
  simp only [liftDeviceObservable,Recorder.extension,Recorder.gate_contact,
    submatrix_apply,kroneckerMap_apply,one_apply,actual,Equiv.prodCongr_apply,
    Equiv.refl_apply,Equiv.prodAssoc_symm_apply,Prod.map,Equiv.symm_apply_apply]
  change (Recorder.contact k).permMatrix ℂ (i.1,i.2.1) (j.1,j.2.1) *
    (if i.2.2 = j.2.2 then 1 else 0) = (wire k r).permMatrix ℂ i j
  simp only [Recorder.permutation_entry]
  have he : wire k r i = j ↔ Recorder.contact k (i.1,i.2.1) = (j.1,j.2.1) ∧ i.2.2 = j.2.2 := by
    change (Equiv.prodAssoc _ _ _) (Recorder.contact k (i.1,i.2.1),i.2.2) = j ↔ _
    rw [Equiv.apply_eq_iff_eq_symm_apply,Prod.mk.injEq]
    rfl
  simp only [he]
  split_ifs <;> simp_all

theorem tester_raw_entry {I : Inventory} (S : Schedule I) (r : ℕ)
    (U : Mat (Fin r × Payload I)) (i j : Raw S r) :
    (liftTesterObservable (Recorder.extension S) r U).submatrix (actual S r) (actual S r) i j =
      (if i.1 = j.1 then 1 else 0) * U (i.2.2,i.2.1) (j.2.2,j.2.1) := by
  simp [liftTesterObservable,actual,one_apply,kroneckerMap_apply,Prod.swap]

theorem tester_raw_mulVec {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (k : Cut S) (v : Raw S r → ℂ) (x : Raw S r) :
    ((liftTesterObservable (Recorder.extension S) r (t.gate k)).submatrix
      (actual S r) (actual S r) *ᵥ v) x =
      ∑ z : Payload I × Fin r, t.gate k (x.2.2,x.2.1) (z.2,z.1) * v (x.1,z) := by
  simp only [mulVec,dotProduct,tester_raw_entry]
  rw [Fintype.sum_prod_type]
  simp [ite_mul,Finset.sum_ite_irrel]

theorem joint_raw_mulVec {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (k : Cut S) (v : Raw S r → ℂ) :
    ((jointGate (Recorder.extension S) t k).submatrix (actual S r) (actual S r)) *ᵥ v =
      step t k v := by
  rw [jointGate_as_product,
    ← submatrix_mul_equiv _ _ (actual S r) (actual S r) (actual S r),
    ← mulVec_mulVec,device_raw,permMatrix_mulVec]
  ext x
  exact tester_raw_mulVec t k (v ∘ wire k r) x

/-- The independent routed tester amplitudes reproduce the entire actual pure
recorder history, including all retained stocks and all tester references. -/
theorem run_amplitudes {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) (n : ℕ) :
    (run (Recorder.extension S) t n).submatrix (actual S r) (actual S r) =
      pureMatrix (amplitudes t Recorder.epr n) := by
  induction n with
  | zero =>
    ext i j
    simp [run,initialState,Recorder.extension,Recorder.source,Recorder.initialVector,
      actual,amplitudes,pureMatrix,kroneckerMap_apply,star_mul]
    ring
  | succ n ih =>
    rw [run,amplitudes]
    split_ifs with h
    · rw [← evolve_submatrix_equiv (actual S r),ih]
      change evolve _ (pureMatrix _) = _
      unfold evolve
      rw [← pureMatrix_mulVec,joint_raw_mulVec]
    · exact ih

theorem step_scale {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (k : Cut S)
    (v : Raw S r → ℂ) (c : ℂ) : step t k (c • v) = c • step t k v := by
  ext x
  simp only [step,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem amplitudes_scale {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r)
    (φ : Recorder.Stock S → ℂ) (c : ℂ) (n : ℕ) :
    amplitudes t (c • φ) n = c • amplitudes t φ n := by
  induction n with
  | zero => ext x; simp [amplitudes,mul_assoc]
  | succ n ih =>
    simp only [amplitudes]
    split_ifs
    · rw [ih,step_scale]
    · exact ih

theorem pureMatrix_scale {a : Type} (v : a → ℂ) (c : ℂ) :
    pureMatrix (c • v) = (Complex.normSq c : ℂ) • pureMatrix v := by
  ext i j
  simp only [pureMatrix,Pi.smul_apply,smul_apply,smul_eq_mul,star_mul]
  rw [← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

end History
end ScheduleLaw
