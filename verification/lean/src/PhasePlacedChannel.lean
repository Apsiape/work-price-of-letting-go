import PhaseOperationalFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.Frobenius
namespace ScheduleLaw.Blueprint.PhasePlacedChannel
open PhaseVectorDistance PhasePacketMap
variable {p : Type} [Fintype p] [DecidableEq p]

/-- Local square gates compared on the old state with the literal phase
packet, with every unheld carrier and tester memory retained. -/
theorem channel (I : Inventory) {b N : ℕ} (r : ℕ) (A : Finset (Fin I.count))
    (e : Fin N ≃ Fin b × p)
    (V : Mat (PhaseOperationalFrame.Local I b A × p)) (hV : IsUnitary V)
    (U : Mat (PhaseOperationalFrame.Local I b A)) (hU : IsUnitary U)
    (v : p → ℂ) (hv : ‖vector v‖=1) (ρ : Density (Fin b × (Payload I × Fin r))) :
    traceDistance
      (evolve (FactoryPlacement.place (PhaseOperationalFrame.contactFrame I r A e) V)
        ((ρ.matrix ⊗ₖ pureMatrix v).submatrix (PhaseOperationalFrame.global I r e)
          (PhaseOperationalFrame.global I r e)))
      (((evolve (FactoryPlacement.place (PhaseOperationalFrame.old I b r A) U) ρ.matrix) ⊗ₖ pureMatrix v).submatrix
        (PhaseOperationalFrame.global I r e) (PhaseOperationalFrame.global I r e))≤
      ‖(V*embed v-embed v*U : Matrix (PhaseOperationalFrame.Local I b A × p)
        (PhaseOperationalFrame.Local I b A) ℂ)‖ := by
  let F := PhaseOperationalFrame.old I b r A
  let E := PhaseOperationalFrame.contactFrame I r A e
  let ρ' : Density (PhaseOperationalFrame.Local I b A × PhaseOperationalFrame.Env I r A) :=
    ⟨ρ.matrix.submatrix F.symm F.symm,ρ.positive.submatrix _,by
      rw [submatrix_trace_equiv]; exact ρ.normalized⟩
  have hc := PhasePacketMixed.channel V hV U hU v hv ρ'
  have he := TraceMarginal.reindex_distance E.symm
    (evolve (FactoryPlacement.place E V) ((ρ.matrix ⊗ₖ pureMatrix v).submatrix
      (PhaseOperationalFrame.global I r e) (PhaseOperationalFrame.global I r e)))
    (((evolve (FactoryPlacement.place F U) ρ.matrix) ⊗ₖ pureMatrix v).submatrix
      (PhaseOperationalFrame.global I r e) (PhaseOperationalFrame.global I r e))
  rw [FactoryPlacement.whole_evolution,PhaseOperationalFrame.factor,PhaseOperationalFrame.factor,
    FactoryPlacement.whole_evolution,← PhasePacketMixed.attach_evolve] at he
  exact he.symm.le.trans hc

end ScheduleLaw.Blueprint.PhasePlacedChannel
