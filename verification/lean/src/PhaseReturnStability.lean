import PhaseDensityTensor

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseReturnStability
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem distance_symm {c : Type} [Fintype c] [DecidableEq c] (X Y : Mat c) :
    traceDistance X Y=traceDistance Y X := by
  unfold traceDistance
  rw [ClassicalFlag.traceNorm_eq_library,ClassicalFlag.traceNorm_eq_library]
  have h : X-Y=-(Y-X) := by abel
  rw [h,Matrix.traceNorm_neg]

/-- Full-state accuracy controls the original controller/all-rest return,
without discarding correlations in either state. -/
theorem whole_rest (ρC : Density a) (X Y : Mat (a × b)) (δ η : ℝ)
    (hXY : traceDistance X Y≤δ)
    (hY : traceDistance Y (ρC.matrix ⊗ₖ partialLeft Y)≤η) :
    traceDistance X (ρC.matrix ⊗ₖ partialLeft X)≤η+2*δ := by
  have hrest : traceDistance (ρC.matrix ⊗ₖ partialLeft Y) (ρC.matrix ⊗ₖ partialLeft X)≤δ := by
    rw [PhaseDensityTensor.distance,distance_symm (partialLeft Y) (partialLeft X)]
    exact (TraceMarginal.left_distance X Y).trans hXY
  have h1 := FactoryOutput.distance_triangle X Y (ρC.matrix ⊗ₖ partialLeft Y)
  have h2 := FactoryOutput.distance_triangle X (ρC.matrix ⊗ₖ partialLeft Y) (ρC.matrix ⊗ₖ partialLeft X)
  linarith

end ScheduleLaw.Blueprint.PhaseReturnStability
