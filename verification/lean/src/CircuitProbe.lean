import SourceContraction
import OwnedEnergy

/-! Signed energy probes may be carried through the actual future unitary
circuit without changing their trace. No measurement, positivity or
independence premise is added for the probe matrix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

def advance {I : Inventory} {S : Schedule I} (e : Extension S) {r : ℕ} (t : Tester S r)
    (start : ℕ) : ℕ → Mat (Global e r) → Mat (Global e r)
  | 0, ρ => ρ
  | n+1, ρ => if h : start+n < 2*S.visits+1 then
      evolve (jointGate e t ⟨start+n,h⟩) (advance e t start n ρ) else advance e t start n ρ

theorem advance_trace {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (start n : ℕ) (ρ : Mat (Global e r)) :
    (advance e t start n ρ).trace = ρ.trace := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [advance]
    split_ifs
    · rw [evolve_trace _ _ (jointGate_unitary e t _),ih]
    · exact ih

theorem advance_run {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (start n : ℕ) :
    advance e t start n (run e t start) = run e t (start+n) := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
    rw [show start+(n+1) = (start+n)+1 by omega,run,advance]
    split_ifs <;> rw [ih]

def terminalProbe {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (H : Mat (Global e r)) : Mat (Global e r) :=
  advance e t n (2*S.visits+1-n) (H * run e t n)

theorem terminalProbe_trace {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (H : Mat (Global e r)) :
    (terminalProbe e t n H).trace.re = energy H (run e t n) := by
  rw [terminalProbe,advance_trace]
  rfl

def carrierProbe {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (c : Fin I.count) : Mat (Global e r) :=
  terminalProbe e t n (liftDeviceObservable e r (carrierObservable I e.b c))

theorem carrierProbe_trace {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) (c : Fin I.count) :
    (carrierProbe e t n c).trace.re = carrierEnergy e (run e t n) c := by
  rw [carrierProbe,terminalProbe_trace,carrierEnergy_as_observable]

theorem handoff_terminal_probes {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) :
    handoff e t = ∑ v : Fin S.visits,
      ((carrierProbe e t ((S.position (v,true)).val+1) (S.carrier v)).trace.re -
        (carrierProbe e t ((S.position (v,false)).val+1) (S.carrier v)).trace.re) := by
  simp only [carrierProbe_trace]
  rfl

end ScheduleLaw.History.Wire
