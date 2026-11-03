import PhaseShiftPacket
import PhaseShellColumns

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseGateColumn
open PhaseLatticeBox PhasePacketDensity PhaseShiftPacket FinitePhaseShell
variable {s ι : Type} [Fintype s] [DecidableEq s] [Fintype ι] [DecidableEq ι]

theorem complete_of_bounds (a : s → PhaseLatticeBox.Lattice ι) (ha : ∀ j k,0≤a j k ∧ a j k≤1)
    (L : ℕ) (y : State (ι:=s) (box ι L)) (hy : ∀ k,0≤y.2.val k ∧ y.2.val k<(L : ℤ)) :
    Complete a (box ι L) (tag a (box ι L) y) := by
  intro j
  apply (box_mem _ _).mpr
  intro k
  have h1 := ha y.1 k
  have h2 := ha j k
  have hk := hy k
  change -2≤y.2.val k+a y.1 k-a j k ∧ y.2.val k+a y.1 k-a j k≤(L : ℤ)+1
  omega

def column (a : s → PhaseLatticeBox.Lattice ι) (L : ℕ) (U : Mat s) (j : s) : State (ι:=s) (box ι L) → ℂ :=
  fun x => ∑ y : ↥(box ι L),FinitePhaseShell.gate a (box ι L) U x (j,y)*packet L y

theorem column_formula (a : s → PhaseLatticeBox.Lattice ι) (ha : ∀ j k,0≤a j k ∧ a j k≤1)
    (L : ℕ) (U : Mat s) (j : s) (x : State (ι:=s) (box ι L)) :
    column a L U j x=U x.1 j*raw L (x.2.val+a x.1-a j) := by
  have hc (y : ↥(box ι L)) :
      FinitePhaseShell.gate a (box ι L) U x (j,y)*packet L y=
        (if x.2.val+a x.1=y.val+a j then U x.1 j else 0)*packet L y := by
    by_cases hp : packet L y=0
    · simp only [hp,mul_zero]
    have hy := raw_support L y.val hp
    have ht := complete_of_bounds a ha L (j,y) hy
    rw [PhaseShellColumns.complete_column a (box ι L) U x (j,y) ht]
    by_cases he : x.2.val+a x.1=y.val+a j
    · have htag : tag a (box ι L) x=tag a (box ι L) (j,y) := Subtype.ext he
      rw [if_pos htag,if_pos he]
    · have htag : tag a (box ι L) x≠tag a (box ι L) (j,y) := by
        intro h
        exact he (congrArg Subtype.val h)
      rw [if_neg htag,if_neg he]
  unfold column
  simp_rw [hc]
  let z := x.2.val+a x.1-a j
  have hval (y : ↥(box ι L)) : x.2.val+a x.1=y.val+a j ↔ y.val=z := by
    constructor
    · intro h
      dsimp only [z]
      rw [h]
      abel
    · intro h
      rw [h]
      dsimp only [z]
      abel
  by_cases hz : z∈box ι L
  · let y0 : ↥(box ι L) := ⟨z,hz⟩
    have he (y : ↥(box ι L)) : x.2.val+a x.1=y.val+a j ↔ y=y0 := by
      rw [hval]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    simp_rw [he]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl
  · have hn (y : ↥(box ι L)) : ¬x.2.val+a x.1=y.val+a j := by
      intro h
      apply hz
      rw [← (hval y).mp h]
      exact y.property
    simp only [hn,if_false,zero_mul,Finset.sum_const_zero]
    rw [raw_outside L z hz,mul_zero]

end ScheduleLaw.Blueprint.PhaseGateColumn
