import PhaseHardwareReadouts
import PhaseHandoffContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseHardwareComparison
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}
variable (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k))

local notation "q" => PhaseHardware.hardware p hD φ Hφ G hG hlocal
local notation "idle" => IdleExtension.extension p.extension (PhaseHardware.phaseStock hD φ)

def Close (δ : ℝ) : Prop := ∀ z (t : Tester S z) n,n≤2*S.visits+1 →
  traceDistance (run (q).extension t n) (run idle t n)≤δ

theorem observer (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ)
    {z : ℕ} (t : Tester S z) (n : ℕ) (hn : n≤2*S.visits+1) :
    traceDistance (partialLeft (run (q).extension t n)) (partialLeft (run p.extension t n))≤δ := by
  have he := TraceMarginal.left_distance (run (q).extension t n) (run idle t n)
  rw [IdleExtension.observerRun_idle] at he
  exact he.trans (h z t n hn)

theorem service (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ) :
    Approximates (q).extension p.extension δ := by
  intro z t
  exact observer p hD φ Hφ G hG hlocal δ h t _ le_rfl

theorem body (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ) {z : ℕ} (t : Tester S z) :
    traceDistance (bodyOutput (q).extension t) (bodyOutput idle t)≤δ :=
  (TraceMarginal.right_distance _ _).trans (h z t _ le_rfl)

theorem controller (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ) {z : ℕ} (t : Tester S z) :
    traceDistance (Driven.controllerFinal q t)
      (((Driven.controllerFinal p t) ⊗ₖ φ.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)≤δ := by
  letI dc : DecidableEq (Fin (p.c*D)) := inferInstance
  letI dr : DecidableEq (Fin p.w × Fin p.r) := inferInstance
  letI : DecidableEq (Fin (p.c*D) × (Fin p.w × Fin p.r)) := @instDecidableEqProd _ _ dc dr
  have he := TraceMarginal.right_distance
    ((bodyOutput (q).extension t).submatrix (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm)
    ((bodyOutput idle t).submatrix (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm)
  rw [TraceMarginal.reindex_distance (PhaseHardware.split p D).symm
    (bodyOutput (q).extension t) (bodyOutput idle t)] at he
  have hi : partialRight ((bodyOutput idle t).submatrix
      (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm)=
      (((Driven.controllerFinal p t) ⊗ₖ φ.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) := by
    rw [IdleExtension.bodyOutput_idle]
    exact PhaseHardwareReadouts.controller p (bodyOutput p.extension t) φ.matrix
  rw [hi] at he
  exact he.trans (body p hD φ Hφ G hG hlocal δ h t)

theorem rest (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ) {z : ℕ} (t : Tester S z) :
    traceDistance (Driven.batteryReservoirFinal q t) (Driven.batteryReservoirFinal p t)≤δ := by
  letI dc : DecidableEq (Fin (p.c*D)) := inferInstance
  letI dr : DecidableEq (Fin p.w × Fin p.r) := inferInstance
  letI : DecidableEq (Fin (p.c*D) × (Fin p.w × Fin p.r)) := @instDecidableEqProd _ _ dc dr
  have he := TraceMarginal.left_distance
    ((bodyOutput (q).extension t).submatrix (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm)
    ((bodyOutput idle t).submatrix (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm)
  rw [TraceMarginal.reindex_distance (PhaseHardware.split p D).symm
    (bodyOutput (q).extension t) (bodyOutput idle t)] at he
  have hi : partialLeft ((bodyOutput idle t).submatrix
      (PhaseHardware.split p D).symm (PhaseHardware.split p D).symm)=Driven.batteryReservoirFinal p t := by
    rw [IdleExtension.bodyOutput_idle]
    exact PhaseHardwareReadouts.rest p (bodyOutput p.extension t) φ
  rw [hi] at he
  exact he.trans (body p hD φ Hφ G hG hlocal δ h t)

theorem battery (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ) {z : ℕ} (t : Tester S z) :
    traceDistance (Driven.batteryFinal q t) (Driven.batteryFinal p t)≤δ :=
  (TraceMarginal.right_distance _ _).trans (rest p hD φ Hφ G hG hlocal δ h t)

theorem reservoir (δ : ℝ) (h : Close p hD φ Hφ G hG hlocal δ) {z : ℕ} (t : Tester S z) :
    traceDistance (Driven.reservoirFinal q t) (Driven.reservoirFinal p t)≤δ :=
  (TraceMarginal.left_distance _ _).trans (rest p hD φ Hφ G hG hlocal δ h t)

end ScheduleLaw.Blueprint.PhaseHardwareComparison
