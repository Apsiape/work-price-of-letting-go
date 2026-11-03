import FactoryPackedReturn
import FactoryDrivenBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPackedBudgets
open History FactoryPacking FactoryPackedFormation FactoryRegisters

theorem four_bit_gap (x1 x2 x3 x4 : ℝ) (j : Fin 16) :
    |workEnergy x1 x2 x3 x4 j-workEnergy x1 x2 x3 x4 nominal| ≤
      |x1|+|x2|+|x3|+|x4| := by
  have hc (x : ℝ) (p : Prop) [Decidable p] : |(if p then x else 0)-x|≤|x| := by
    by_cases hp : p <;> simp [hp]
  have hnom : workEnergy x1 x2 x3 x4 nominal=x1+x2+x3+x4 := by
    simp only [workEnergy,nominal,Equiv.symm_apply_apply,FactoryWorkFlags.nominal,if_true]
  rw [hnom]
  unfold workEnergy
  let w := workEquiv.symm j
  change |((if w.1=1 then x1 else 0)+(if w.2.1=1 then x2 else 0)+
    (if w.2.2.1=1 then x3 else 0)+(if w.2.2.2=1 then x4 else 0))-(x1+x2+x3+x4)|≤_
  let a := (if w.1=1 then x1 else 0)-x1
  let b := (if w.2.1=1 then x2 else 0)-x2
  let c := (if w.2.2.1=1 then x3 else 0)-x3
  let d := (if w.2.2.2=1 then x4 else 0)-x4
  have he : ((if w.1=1 then x1 else 0)+(if w.2.1=1 then x2 else 0)+
      (if w.2.2.1=1 then x3 else 0)+(if w.2.2.2=1 then x4 else 0))-(x1+x2+x3+x4)=a+b+c+d := by
    dsimp only [a,b,c,d]; ring
  rw [he]
  have h1 := abs_add_le (a+b+c) d
  have h2 := abs_add_le (a+b) c
  have h3 := abs_add_le a b
  have ha := hc x1 (w.1=1)
  have hb := hc x2 (w.2.1=1)
  have hc0 := hc x3 (w.2.2.1=1)
  have hd := hc x4 (w.2.2.2=1)
  change |a|≤|x1| at ha
  change |b|≤|x2| at hb
  change |c|≤|x3| at hc0
  change |d|≤|x4| at hd
  linarith

/-- All six original Driven.Meets fields for the actual packed Formation.
The remaining numerical input is its actual nominal battery probability. -/
theorem actual_budgets {d m D r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β≠0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ) {r : Type} [Fintype r] [DecidableEq r]
    (e : Fin D ≃ (Fin m → Fin d) × r)
    (U1 : Mat ((Fin m → Fin d) × (Fin 2 × Fin r1)))
    (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (U4 : Mat (Fin D × (Fin 2 × Fin r4)))
    (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V) (hu4 : IsUnitary U4) :
    let U := circuit e U1 U2 V U4
    let hU : IsUnitary U := by convert circuit_unitary e U1 U2 V U4 hu1 hu2 hv hu4 using 1
    let F := formation hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4 x1 x2 x3 x4 U hU
    ∀ η f : ℝ,0 < η → 0 ≤ f →
      ∃ ε : ℝ,0 < ε ∧
        ((∀ z (t : Tester F.schedule z),
          1-(Driven.batteryFinal F.hardware t F.hardware.nominalLevel F.hardware.nominalLevel).re ≤ min ε f) →
          Driven.Meets F.hardware (FactoryDrivenBudgets.budget η f (|x1|+|x2|+|x3|+|x4|))) := by
  dsimp only
  intro η f hη hf
  apply FactoryDrivenBudgets.meets _ η f (|x1|+|x2|+|x3|+|x4|) hη hf (by positivity)
  · intro j
    exact four_bit_gap x1 x2 x3 x4 j
  · exact FactoryPackedReturn.whole_product hd hm hD h1 h2 h4 β hβ τ q hq H1 H2 H4
      x1 x2 x3 x4 e U1 U2 V U4 hu1 hu2 hv hu4

end ScheduleLaw.Blueprint.FactoryPackedBudgets
