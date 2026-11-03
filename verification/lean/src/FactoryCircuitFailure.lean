import FactoryExtractorBound
import FactoryPreparationTransport
import FactoryWorkState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryCircuitFailure
open History FactoryRegisters

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def state {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (code : Density c) (batch : Density b) (γ1 : Density t1)
    (γ2 : Density t2) (γ4 : Density t4) (fresh : Density c)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    Density (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) := by
  let U := circuit s U1 U2 V U4
  let ρ := FactoryInitializer.matrix code batch γ1 γ2 γ4 fresh
  have hU : IsUnitary U := circuit_unitary s U1 U2 V U4 h1 h2 hV h4
  have hp := evolve_density U ρ hU (FactoryInitializer.positive code batch γ1 γ2 γ4 fresh)
    (FactoryInitializer.normalized code batch γ1 γ2 γ4 fresh)
  exact ⟨evolve U ρ,hp.1,hp.2⟩

/-- The literal initialized complete circuit, with an actually constructed
extractor, satisfies the sixteen-level nominal failure bound. -/
theorem failure {b : Type} [Fintype b] [DecidableEq b] {D R r1 r2 : ℕ}
    (hD : 0 < D) (hR : 0 < R) (β : ℝ) (hβ : 0 < β)
    (e : Fin D ≃ b × Fin R) (P : Mat b) (hP : P.IsHermitian) (hPi : P*P=P) (htr : P.trace=1)
    (code : Density (Fin D)) (batch : Density b) (γ1 : Density (Fin r1))
    (γ2 : Density (Fin r2)) (fresh : Density (Fin D))
    (U1 : Mat (b × (Fin 2 × Fin r1))) (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V)
    (ε1 ε2 ε4 : ℝ) (hε1 : 0 ≤ ε1) (hε4 : 0 < ε4) (hε41 : ε4 ≤ 1)
    (hprep : 1-ε1 ≤ energy P (partialRight
      (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix)))))
    (hw1 : 1-ε1 ≤ energy ((1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin r1))))
      (evolve U1 (batch.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ1.matrix))))
    (hw2 : 1-ε2 ≤ energy ((1 : Mat (Fin D)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin r2))))
      (evolve U2 (code.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ γ2.matrix)))) :
    ∃ C4 : SupportConverter β (FiniteFlat.zeroHamiltonian D) (Real.log ((D : ℝ)/R)/β-1),
      1-((FactoryWorkState.density (state e code batch γ1 γ2
        (FactoryPackedStock.gibbsDensity C4.r_pos β C4.HR) fresh U1 U2 V C4.U
          h1 h2 hV C4.unitary)).matrix FactoryWorkFlags.nominal FactoryWorkFlags.nominal).re ≤
            2*ε1+ε2+ε4 := by
  obtain ⟨C4,h4⟩ := FactoryExtractorBound.extract hD hR β hβ e P hP hPi htr code batch γ1 γ2 fresh
    U1 U2 V h1 h2 hV ε1 ε4 hε4 hε41 hprep
  let γ4 := FactoryPackedStock.gibbsDensity C4.r_pos β C4.HR
  let ρ := state e code batch γ1 γ2 γ4 fresh U1 U2 V C4.U h1 h2 hV C4.unitary
  refine ⟨C4,?_⟩
  apply FactoryWorkState.failure ρ ε1 ε2 ε4 hε1 hε4.le
  · have hp := FactoryInitializedFlags.first_probability e code batch γ1 γ2 γ4 fresh U1 U2 V C4.U
      h2 hV C4.unitary
    have hb := hw1
    rw [← hp] at hb
    simpa only [FactoryFlagEffects.success_sum] using hb
  · have hp := FactoryInitializedFlags.second_probability e code batch γ1 γ2 γ4 fresh U1 U2 V C4.U
      h1 hV C4.unitary
    have hb := hw2
    rw [← hp] at hb
    simpa only [FactoryFlagEffects.success_sum] using hb
  · simpa only [FactoryFlagEffects.success_sum] using
      (FactoryInitializedFlags.third_probability e code batch γ1 γ2 γ4 fresh U1 U2 V C4.U
        h1 h2 hV C4.unitary)
  · simpa only [FactoryFlagEffects.success_sum] using h4

end ScheduleLaw.Blueprint.FactoryCircuitFailure
