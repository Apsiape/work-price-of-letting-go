import FinitePhaseShell

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseShellColumns
open FinitePhaseShell
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup G] [DecidableEq G]

theorem distinct_shells (a : ι → G) (B : Finset G) (U : Mat ι)
    (x y : State (ι:=ι) B) (h : tag a B x≠tag a B y) : gate a B U x y=0 := by
  exact Matrix.blockDiagonal'_apply_ne (block a B U)
    (frame a B x).2 (frame a B y).2 h

theorem complete_column (a : ι → G) (B : Finset G) (U : Mat ι)
    (x y : State (ι:=ι) B) (hy : Complete a B (tag a B y)) :
    gate a B U x y=if tag a B x=tag a B y then U x.1 y.1 else 0 := by
  by_cases h : tag a B x=tag a B y
  · rw [if_pos h]
    exact complete_action a B U (tag a B y) hy ⟨x,h⟩ ⟨y,rfl⟩
  · rw [if_neg h]
    exact distinct_shells a B U x y h

end ScheduleLaw.Blueprint.PhaseShellColumns
