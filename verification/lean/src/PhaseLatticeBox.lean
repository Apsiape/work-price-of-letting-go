import FinitePhaseShell
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseLatticeBox
variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Lattice (ι : Type) := ι → ℤ

def box (ι : Type) [Fintype ι] (L : ℕ) : Finset (Lattice ι) :=
  Fintype.piFinset (fun _ => Finset.Icc (-2) ((L : ℤ)+1))

def label (i : ι) : Lattice ι := fun j => if j=i then 1 else 0

def frequency (E : ι → ℝ) : Lattice ι →+ ℝ where
  toFun x := ∑ i,(x i : ℝ)*E i
  map_zero' := by simp
  map_add' x y := by simp [Int.cast_add,add_mul,Finset.sum_add_distrib]

theorem frequency_label (E : ι → ℝ) (i : ι) : frequency E (label i)=E i := by
  simp [frequency,label]

theorem box_mem (L : ℕ) (x : Lattice ι) : x∈box ι L ↔ ∀ i,-2≤x i ∧ x i≤(L : ℤ)+1 := by
  simp only [box,Fintype.mem_piFinset,Finset.mem_Icc]

def boxFrame (L : ℕ) : (ι → Fin (L+4)) ≃ ↥(box ι L) where
  toFun x := ⟨fun i => ((x i).val : ℤ)-2,(box_mem _ _).mpr (fun i => by
    have hx := (x i).isLt
    omega)⟩
  invFun x i := ⟨(x.val i+2).toNat,by
    have hx := (box_mem L x.val).mp x.property i
    omega⟩
  left_inv x := by
    funext i
    apply Fin.ext
    simp only
    omega
  right_inv x := by
    apply Subtype.ext
    funext i
    have hx := (box_mem L x.val).mp x.property i
    simp only
    omega

theorem box_card (L : ℕ) : (box ι L).card=(L+4)^Fintype.card ι := by
  have h := Fintype.card_congr (boxFrame (ι:=ι) L)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using h.symm

/-- Every packet-supported input lies in a complete shell. The padded box
therefore acts by the actual full unitary on all nonzero input columns. -/
theorem complete_of_interior (L : ℕ) (y : FinitePhaseShell.State (ι:=ι) (box ι L))
    (hy : ∀ k,0≤y.2.val k ∧ y.2.val k<(L : ℤ)) :
    FinitePhaseShell.Complete label (box ι L) (FinitePhaseShell.tag label (box ι L) y) := by
  intro i
  apply (box_mem _ _).mpr
  intro k
  have hk := hy k
  change -2 ≤ y.2.val k+label y.1 k-label i k ∧
    y.2.val k+label y.1 k-label i k ≤ (L : ℤ)+1
  simp only [label]
  split_ifs <;> omega

end ScheduleLaw.Blueprint.PhaseLatticeBox
