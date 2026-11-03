import SupportStock
import SupportCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.SupportGenerators

def sourceIndex {d : ℕ} (i : Fin d) : Fin (d+(d+1)) := Fin.castAdd (d+1) i
def targetIndex {d : ℕ} (i : Fin d) : Fin (d+(d+1)) := Fin.natAdd d i.castSucc
def workIndex (d : ℕ) : Fin (d+(d+1)) := Fin.natAdd d (Fin.last d)
def direction {n : ℕ} (i : Fin n) : Fin n → ℤ := Pi.single i 1
def generators {d : ℕ} (EP EQ : Fin d → ℝ) (x : ℝ) : Fin (d+(d+1)) → ℝ :=
  Fin.append EP (Fin.snoc EQ x)

theorem direction_energy {n : ℕ} (ω : Fin n → ℝ) (i : Fin n) :
    SupportTiles.coordinateEnergy ω (direction i) = ω i := by
  simp [SupportTiles.coordinateEnergy,direction,Pi.single_apply]

theorem source_energy {d : ℕ} (EP EQ : Fin d → ℝ) (x : ℝ) (i : Fin d) :
    SupportTiles.coordinateEnergy (generators EP EQ x) (direction (sourceIndex i)) = EP i := by
  rw [direction_energy]
  exact Fin.append_left _ _ _

theorem target_energy {d : ℕ} (EP EQ : Fin d → ℝ) (x : ℝ) (i : Fin d) :
    SupportTiles.coordinateEnergy (generators EP EQ x) (direction (targetIndex i)) = EQ i := by
  rw [direction_energy]
  simp only [generators,targetIndex,Fin.append_right,Fin.snoc_castSucc]

theorem work_energy {d : ℕ} (EP EQ : Fin d → ℝ) (x : ℝ) :
    SupportTiles.coordinateEnergy (generators EP EQ x) (direction (workIndex d)) = x := by
  rw [direction_energy]
  simp only [generators,workIndex,Fin.append_right,Fin.snoc_last]

theorem shift_bound {d : ℕ} (i j : Fin d) (k : Fin (d+(d+1))) :
    -1 ≤ direction (sourceIndex i) k-direction (targetIndex j) k-direction (workIndex d) k ∧
    direction (sourceIndex i) k-direction (targetIndex j) k-direction (workIndex d) k ≤ 1 := by
  have hst : sourceIndex i ≠ targetIndex j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [sourceIndex,targetIndex,Fin.val_castAdd,Fin.val_natAdd,Fin.val_castSucc] at hval
    omega
  have hsw : sourceIndex i ≠ workIndex d := by
    intro h
    have hval := congrArg Fin.val h
    simp only [sourceIndex,workIndex,Fin.val_castAdd,Fin.val_natAdd,Fin.val_last] at hval
    omega
  have htw : targetIndex j ≠ workIndex d := by
    intro h
    have hval := congrArg Fin.val h
    simp only [targetIndex,workIndex,Fin.val_natAdd,Fin.val_castSucc,Fin.val_last] at hval
    omega
  simp only [direction,Pi.single_apply]
  split_ifs <;> simp_all

end ScheduleLaw.Blueprint.SupportGenerators
