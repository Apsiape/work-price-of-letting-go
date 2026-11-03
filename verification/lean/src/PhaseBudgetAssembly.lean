import PhaseBudgetPhysical
import PhaseBudgetEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.PhaseBudgetAssembly
open History PhaseBudgetPhysical
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def uniform (x : ℝ) : Budget := ⟨x,x,x,x,x,x⟩

theorem coefficient_bounds (p : Driven S β) :
    2≤coefficient p ∧ energyCoeff p≤coefficient p ∧ failureCoeff p≤coefficient p ∧ tailCoeff p≤coefficient p := by
  have hh : 0≤handoffBound S := by unfold handoffBound; positivity
  have he : 0≤energyCoeff p := by unfold energyCoeff; positivity
  have hf : 0≤failureCoeff p := by unfold failureCoeff; positivity
  have ht : 0≤tailCoeff p := by unfold tailCoeff; positivity
  dsimp only [coefficient]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Assemble all six original budgets for the same specified hardware.
The history and conservation inputs are separately proved for the concrete
spectral hardware before this lemma is used to close the phase theorem. -/
theorem realizes (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k))
    (rank L : ℕ) (K η ζ : ℝ) (hK : 0≤K) (hη : 0<η) (hζ : 0<ζ)
    (b : Budget) (hb : Driven.Meets p b) (hs : SmallBudget b η)
    (hdef : ∀ z (t : Tester S z),|Driven.defect p t|≤2*η)
    (hdim : D=(L+4)^rank)
    (hclose : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal (K/(L+1 : ℝ)))
    (hcon : ∀ k,Conserves ((PhaseHardware.hardware p hD φ Hφ G hG hlocal).extension.gate k)
      ((PhaseHardware.hardware p hD φ Hφ G hG hlocal).bodyHamiltonian ⊗ₖ (1 : Mat (Payload I))+
        (1 : Mat (Fin (PhaseHardware.hardware p hD φ Hφ G hG hlocal).extension.b)) ⊗ₖ payloadHamiltonian I))
    (hservice : K/(L+1 : ℝ)≤ζ) (hphysical : coefficient p*(K/(L+1 : ℝ))≤ζ)
    (hcontroller : PhaseEntropyLimit.modulus p.c rank K L≤ζ)
    (hbattery : PhaseEntropyLimit.modulus p.w 0 K L≤ζ) :
    ∃ (d : Engine S β) (B : Budget),Approximates d.extension p.extension ζ ∧ MeetsBudget d B ∧
      SmallBudget B (4*η+ζ) ∧ nominalDebit d≤Driven.nominalDebit p+ζ ∧
        faithfulRelativeEntropy d.controller.matrix (gibbs β d.HC)/β≤d.capital := by
  let q := PhaseHardware.hardware p hD φ Hφ G hG hlocal
  let d := PhaseHardware.toEngine q hcon
  let B := uniform (4*η+ζ)
  have hδ : 0≤K/(L+1 : ℝ) := div_nonneg hK (by positivity)
  rcases coefficient_bounds p with ⟨h2,hE,hF,hT⟩
  have h2δ : 2*(K/(L+1 : ℝ))≤ζ := (mul_le_mul_of_nonneg_right h2 hδ).trans hphysical
  have hEδ : energyCoeff p*(K/(L+1 : ℝ))≤ζ := (mul_le_mul_of_nonneg_right hE hδ).trans hphysical
  have hFδ : failureCoeff p*(K/(L+1 : ℝ))≤ζ := (mul_le_mul_of_nonneg_right hF hδ).trans hphysical
  have hTδ : tailCoeff p*(K/(L+1 : ℝ))≤ζ := (mul_le_mul_of_nonneg_right hT hδ).trans hphysical
  rcases hs with ⟨hsP,hsE,hsS,hsB,hsF,hsT⟩
  have hm : Driven.Meets q B := by
    have hB0 : 0≤4*η+ζ := by positivity
    refine ⟨⟨hB0,hB0,hB0,hB0,hB0,hB0⟩,?_⟩
    intro z t
    rcases hb.2 z t with ⟨hP,hE,hS,hB,hF,hT⟩
    have hp := return_bound p hD φ Hφ G hG hlocal _ η hclose t (hP.trans hsP)
    have he := controller_bound p hD φ Hφ G hG hlocal _ η hclose hcon t (hE.trans hsE) (hdef z t)
    have hsc := PhaseBudgetEntropy.controller p hD φ Hφ G hG hlocal rank L K η hdim hclose t (hS.trans hsS)
    have hsb := PhaseBudgetEntropy.battery p hD φ Hφ G hG hlocal L K η hclose t (hB.trans hsB)
    have hfc := failure_bound p hD φ Hφ G hG hlocal _ η hclose t (hF.trans hsF)
    have htc := tail_bound p hD φ Hφ G hG hlocal _ η hclose t (hT.trans hsT)
    change Driven.controllerProductDefect q t≤4*η+ζ ∧ |Driven.controllerEnergyChange q t|≤4*η+ζ ∧
      |Driven.controllerEntropyChange q t|≤4*η+ζ ∧ entropy (Driven.batteryFinal q t)≤4*η+ζ ∧
      1-(Driven.batteryFinal q t q.nominalLevel q.nominalLevel).re≤4*η+ζ ∧
      Driven.batteryAbsoluteTail q t≤4*η+ζ
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  refine ⟨d,B,?_,?_,?_,?_,?_⟩
  · have h := PhaseHardwareComparison.service p hD φ Hφ G hG hlocal _ hclose
    intro z t
    exact (h z t).trans hservice
  · exact hm
  · exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩
  · have hn : nominalDebit d=Driven.nominalDebit p := rfl
    rw [hn]
    linarith
  · exact le_rfl

end ScheduleLaw.Blueprint.PhaseBudgetAssembly
