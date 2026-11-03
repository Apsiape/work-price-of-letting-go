import PhasePlacedChannel
import PhaseSpectralData
import PhaseHardwareHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhaseSpectralOperational
open History PhaseSpectralLabels PhaseSpectralHardware PhaseSpectralData
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def idle (p : Driven S β) (L : ℕ) (hL : 0<L) : Extension S :=
  IdleExtension.extension p.extension (PhaseHardware.phaseStock (dim_pos p L) (controllerPhase p L hL))

def wires (p : Driven S β) (L z : ℕ) := PhaseOperationalFrame.global I z (frame p L)

def ideal (p : Driven S β) (L z : ℕ) (X : Mat (Global p.extension z)) :
    Mat (Fin (p.extension.b*D p L) × (Payload I × Fin z)) :=
  (X ⊗ₖ pureMatrix (PhasePacketDensity.packet (ι:=Index p) L)).submatrix (wires p L z) (wires p L z)

theorem idle_run (p : Driven S β) (L : ℕ) (hL : 0<L) {z : ℕ} (t : Tester S z) (n : ℕ) :
    run (idle p L hL) t n=ideal p L z (run p.extension t n) := by
  unfold idle
  rw [IdleExtension.run_idle]
  change ((run p.extension t n) ⊗ₖ (controllerPhase p L hL).matrix).submatrix
    (IdleExtension.wires p.extension.b (D p L) _) (IdleExtension.wires p.extension.b (D p L) _)=_
  rw [controllerPhase_matrix]
  ext i j
  rfl

theorem old_device (p : Driven S β) (z : ℕ) (k : Cut S) :
    liftDeviceObservable p.extension z (p.extension.gate k)=
      FactoryPlacement.place (PhaseOperationalFrame.old I p.extension.b z (held S k))
        (localContactGate p.extension k) := by
  change (fun i j : Global p.extension z => p.extension.gate k (i.1,i.2.1) (j.1,j.2.1)*
    (if i.2.2=j.2.2 then 1 else 0))=_
  exact PhaseOperationalFrame.old_device I p.extension.b z (held S k) _ _
    (localContactGate_spec p.extension k).2

theorem actual_device (p : Driven S β) (L : ℕ) (hL : 0<L) (z : ℕ) (k : Cut S) :
    liftDeviceObservable (hardware p L hL).extension z (G p L k)=
      FactoryPlacement.place (PhaseOperationalFrame.contactFrame I z (held S k) (frame p L))
        (localGate p L k) := by
  change (fun i j : Fin (p.extension.b*D p L) × (Payload I × Fin z) =>
    G p L k (i.1,i.2.1) (j.1,j.2.1)*(if i.2.2=j.2.2 then 1 else 0))=_
  exact PhaseOperationalFrame.device I z (held S k) (frame p L) (localGate p L k)

theorem idle_device (p : Driven S β) (L : ℕ) (hL : 0<L) (z : ℕ) (k : Cut S) :
    liftDeviceObservable (idle p L hL) z ((idle p L hL).gate k)=
      (liftDeviceObservable p.extension z (p.extension.gate k) ⊗ₖ (1 : Mat (Phase p L))).submatrix
        (wires p L z) (wires p L z) := by
  unfold idle
  rw [IdleExtension.liftDevice_idle]
  ext i j
  simp only [submatrix_apply,kroneckerMap_apply,Matrix.one_apply,wires,PhaseOperationalFrame.global,
    frame,IdleExtension.globalWires,IdleExtension.wires,Equiv.coe_fn_mk,Equiv.trans_apply,
    Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply]
  dsimp only [Prod.map,Equiv.refl]
  simp only [Equiv.coe_fn_mk,(Fintype.equivFin (Phase p L)).symm.injective.eq_iff] <;> rfl

theorem ideal_evolve (p : Driven S β) (L z : ℕ) (M X : Mat (Global p.extension z)) :
    evolve ((M ⊗ₖ (1 : Mat (Phase p L))).submatrix (wires p L z) (wires p L z)) (ideal p L z X)=
      ideal p L z (evolve M X) := by
  unfold ideal
  rw [evolve_submatrix_equiv,IdleExtension.evolve_idle]

theorem device_error (p : Driven S β) (L : ℕ) (hL : 0<L) (z : ℕ) (k : Cut S)
    (ρ : Density (Global p.extension z)) :
    traceDistance
      (evolve (liftDeviceObservable (hardware p L hL).extension z (G p L k)) (ideal p L z ρ.matrix))
      (evolve (liftDeviceObservable (idle p L hL) z ((idle p L hL).gate k)) (ideal p L z ρ.matrix))≤
        cutConstant p k/(L+1 : ℝ) := by
  have h := PhasePlacedChannel.channel I z (held S k) (frame p L)
    (localGate p L k) (PhaseVectorDistance.unitary_instances _ _ _ (localGate_unitary p L k))
    (localContactGate p.extension k)
    (PhaseVectorDistance.unitary_instances _ _ _ (localContactGate_spec p.extension k).1)
    (PhasePacketDensity.packet (ι:=Index p) L) (PhasePacketDensity.norm L hL) ρ
  rw [← actual_device p L hL z k,← old_device p z k] at h
  have hi := ideal_evolve p L z (liftDeviceObservable p.extension z (p.extension.gate k)) ρ.matrix
  rw [← idle_device p L hL z k] at hi
  change traceDistance
    (evolve (liftDeviceObservable (hardware p L hL).extension z (G p L k)) (ideal p L z ρ.matrix))
    (ideal p L z (evolve (liftDeviceObservable p.extension z (p.extension.gate k)) ρ.matrix))≤_ at h
  rw [← hi] at h
  exact h.trans (cut_error p L hL k)

theorem joint_cut (p : Driven S β) (L : ℕ) (hL : 0<L) {z : ℕ} (t : Tester S z) (k : Cut S) :
    traceDistance (evolve (jointGate (hardware p L hL).extension t k) (run (idle p L hL) t k.val))
      (evolve (jointGate (idle p L hL) t k) (run (idle p L hL) t k.val))≤cutConstant p k/(L+1 : ℝ) := by
  let ρ : Density (Global p.extension z) :=
    ⟨run p.extension t k.val,(run_density p.extension t k.val).1,(run_density p.extension t k.val).2⟩
  have h := device_error p L hL z k ρ
  rw [← idle_run p L hL t k.val] at h
  have ht : liftTesterObservable (hardware p L hL).extension z (t.gate k)=
      liftTesterObservable (idle p L hL) z (t.gate k) := rfl
  have h1 : IsUnitary (1 : Mat (Fin (idle p L hL).b)) := by constructor <;> simp
  have hu : IsUnitary (liftTesterObservable (idle p L hL) z (t.gate k)) :=
    PhaseVectorDistance.unitary_instances _ _ _ (unitary_kron h1
      (unitary_submatrix (Equiv.prodComm (Payload I) (Fin z)) (t.unitary k)))
  rw [jointGate_as_product,jointGate_as_product,evolve_mul,evolve_mul,ht,
    FiniteResidue.traceDistance_unitary _ _ _ hu]
  exact h

/-- One specified finite device has uniform full-state accuracy for every
coherent tester and every prefix of the original schedule. -/
theorem close (p : Driven S β) (L : ℕ) (hL : 0<L) :
    PhaseHardwareComparison.Close p (dim_pos p L) (controllerPhase p L hL) (phaseHFin p L)
      (G p L) (G_unitary p L) (G_local p L) (constant p/(L+1 : ℝ)) := by
  have h := PhaseHardwareHistory.from_cut_error p (dim_pos p L) (controllerPhase p L hL)
    (phaseHFin p L) (G p L) (G_unitary p L) (G_local p L)
    (fun k => cutConstant p k/(L+1 : ℝ))
    (fun k => div_nonneg (cut_nonneg p k) (by positivity))
    (fun z t k => joint_cut p L hL t k)
  simpa only [constant,Finset.sum_div] using h

end ScheduleLaw.Blueprint.PhaseSpectralOperational
