import CacheClockAdvance
import CacheFactoryBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheWorkLedger
open History

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

/-- Boundary credit and every original factory work label remain mechanical. -/
def helperEnergy (F : Formation β τ q (n+1)) (z : Fin 2 × Fin F.hardware.w) : ℝ :=
  (if z.1=1 then (n+1 : ℝ)*F.debit else 0)+F.hardware.batteryEnergy z.2

theorem canceled_gap (F : Formation β τ q (n+1)) (j : Fin F.hardware.w) :
    helperEnergy F (1,j)-helperEnergy F (0,F.hardware.initialLevel)=
      F.hardware.batteryEnergy j-F.hardware.batteryEnergy F.hardware.nominalLevel := by
  have hd := F.debit_eq
  unfold Driven.nominalDebit at hd
  simp only [helperEnergy,if_true,Fin.zero_ne_one,if_false,zero_add]
  push_cast at hd
  linarith

theorem successful_energy (F : Formation β τ q (n+1)) :
    helperEnergy F (1,F.hardware.nominalLevel)=helperEnergy F (0,F.hardware.initialLevel) := by
  have h := canceled_gap F F.hardware.nominalLevel
  linarith

theorem absolute_tail (F : Formation β τ q (n+1)) (ρ : Mat (Fin F.hardware.w)) :
    (∑ j, |helperEnergy F (1,j)-helperEnergy F (0,F.hardware.initialLevel)| *(ρ j j).re)=
      ∑ j, |F.hardware.batteryEnergy j-F.hardware.batteryEnergy F.hardware.nominalLevel| *(ρ j j).re := by
  simp only [canceled_gap]

abbrev Work (F : Formation β τ q (n+1)) := Fin 2 × (Fin 2 × Fin F.hardware.w)

def energy (F : Formation β τ q (n+1)) (service : ℝ) (z : Work F) : ℝ :=
  (if z.1=1 then -(F.debit+service) else 0)+helperEnergy F z.2

def initial (F : Formation β τ q (n+1)) : Work F := (0,0,F.hardware.initialLevel)
def nominal (F : Formation β τ q (n+1)) : Work F := (1,0,F.hardware.initialLevel)

theorem nominal_debit (F : Formation β τ q (n+1)) (service : ℝ) :
    energy F service (initial F)-energy F service (nominal F)=F.debit+service := by
  simp [energy,initial,nominal]

theorem boundary_tail (F : Formation β τ q (n+1)) (service : ℝ) (j : Fin F.hardware.w) :
    |energy F service (1,1,j)-energy F service (nominal F)|=
      |F.hardware.batteryEnergy j-F.hardware.batteryEnergy F.hardware.nominalLevel| := by
  unfold energy nominal
  simp only [if_true,add_sub_add_left_eq_sub]
  rw [canceled_gap]

/-- The same main label supplies the cache debit and the bare-service pump.
Its initialized energy change is exactly the signed service debit. -/
theorem pump_change (F : Formation β τ q (n+1)) (service : ℝ) (k : Fin (n+1))
    (j : Fin F.hardware.w) :
    (CacheClockAdvance.clockEnergy n F.debit (CacheClockAdvance.step n k)+
      energy F service (1,(if k=0 then 1 else 0),j))-
      (CacheClockAdvance.clockEnergy n F.debit k+energy F service (0,0,j)) = -service := by
  have h := CacheClockAdvance.clock_change n F.debit k
  by_cases hk : k=0 <;>
    simp [energy,helperEnergy,hk] at * <;> linarith

end ScheduleLaw.Blueprint.CacheWorkLedger
