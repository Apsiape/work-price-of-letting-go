import CacheSourceHistory
import ActualSlackBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.SourceFunctional
open History CacheSourceHistory
variable {I : Inventory} {S : Schedule I}

theorem state_sub {a : Type} [Fintype a] (H X Y : Mat a) :
    energy H (X-Y)=energy H X-energy H Y := (energyLinear H).map_sub X Y

theorem energy_difference {a : Type} [Fintype a] (H X Y A B : Mat a) (p : ℝ)
    (h : X-Y=p • (A-B)) : energy H X-energy H Y=p*(energy H A-energy H B) := by
  have hh := congrArg (energyLinear H) h
  simpa only [map_sub,map_smul,smul_eq_mul,energyLinear] using hh

theorem body_difference (e : Extension S) (ρ σ A B : Density (Fin e.b)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) :
    (bodyOutput (withSource e ρ) t : Mat (Fin e.b))-bodyOutput (withSource e σ) t =
      p • (bodyOutput (withSource e A) t-bodyOutput (withSource e B) t) := by
  have hh := difference e ρ σ A B p h t (2*S.visits+1)
  ext i j
  have he := congrArg (fun M : Mat (Global e z) => partialRight M i j) hh
  simpa only [bodyOutput,finalState,partialRight,Matrix.sub_apply,Matrix.smul_apply,
    Finset.sum_sub_distrib,← Finset.smul_sum] using he

theorem carrier_difference (e : Extension S) (ρ σ A B : Density (Fin e.b)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) (k : ℕ) (c : Fin I.count) :
    carrierEnergy (withSource e ρ) (ScheduleLaw.run (withSource e ρ) t k) c-
      carrierEnergy (withSource e σ) (ScheduleLaw.run (withSource e σ) t k) c =
      p*(carrierEnergy (withSource e A) (ScheduleLaw.run (withSource e A) t k) c-
        carrierEnergy (withSource e B) (ScheduleLaw.run (withSource e B) t k) c) := by
  unfold carrierEnergy
  exact energy_difference _ _ _ _ _ p (difference e ρ σ A B p h t k)

theorem handoff_difference (e : Extension S) (ρ σ A B : Density (Fin e.b)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) :
    handoff (withSource e ρ) t-handoff (withSource e σ) t =
      p*(handoff (withSource e A) t-handoff (withSource e B) t) := by
  unfold handoff
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hr := carrier_difference e ρ σ A B p h t ((S.position (v,true)).val+1) (S.carrier v)
  have ha := carrier_difference e ρ σ A B p h t ((S.position (v,false)).val+1) (S.carrier v)
  nlinarith

theorem physical_difference (β : ℝ) (e : Extension S) (q : Density (Fin e.b))
    (ρ σ A B : Density (Fin e.b)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) :
    physicalLinearized β (withSource e ρ) q t-physicalLinearized β (withSource e σ) q t =
      p*(physicalLinearized β (withSource e A) q t-physicalLinearized β (withSource e B) q t) := by
  have hh := handoff_difference e ρ σ A B p h t
  have he := energy_difference (tangentHamiltonian β q) _ _ _ _ p (body_difference e ρ σ A B p h t)
  have hi := energy_difference (tangentHamiltonian β q) _ _ _ _ p h
  simp only [physicalLinearized,show ∀ X Y : Mat (Fin e.b),energy (tangentHamiltonian β q) (X-Y)=
      energy (tangentHamiltonian β q) X-energy (tangentHamiltonian β q) Y from
        fun X Y => (energyLinear (tangentHamiltonian β q)).map_sub X Y]
  change _ + (_-energy (tangentHamiltonian β q) ρ.matrix)-
    (_+(_-energy (tangentHamiltonian β q) σ.matrix)) =
      p*(_+(_-energy (tangentHamiltonian β q) A.matrix)-
        (_+(_-energy (tangentHamiltonian β q) B.matrix)))
  nlinarith

def bound (β : ℝ) (S : Schedule I) {d : ℕ} (q : Density (Fin d)) : ℝ :=
  handoffBound S+2*‖tangentHamiltonian β q‖

theorem bound_nonneg (β : ℝ) (S : Schedule I) {d : ℕ} (q : Density (Fin d)) : 0 ≤ bound β S q := by
  unfold bound handoffBound
  positivity

theorem physical_abs (β : ℝ) (e : Extension S) (q : Density (Fin e.b))
    {z : ℕ} (t : Tester S z) : |physicalLinearized β e q t| ≤ bound β S q := by
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  have hh : |handoff e t| ≤ handoffBound S := abs_le.mpr ⟨handoff_lower_bound e t,handoff_le e t⟩
  have he := density_energy_abs_le (tangentHamiltonian β q) ρ
  have hi := density_energy_abs_le (tangentHamiltonian β q) e.source
  unfold physicalLinearized bound
  rw [show energy (tangentHamiltonian β q) (bodyOutput e t-e.source.matrix)=
    energy (tangentHamiltonian β q) (bodyOutput e t)-energy (tangentHamiltonian β q) e.source.matrix from
      (energyLinear (tangentHamiltonian β q)).map_sub _ _]
  exact (abs_add_le _ _).trans ((add_le_add hh ((abs_sub _ _).trans (add_le_add he hi))).trans (le_of_eq (by ring)))

theorem rare_error (β : ℝ) (e : Extension S) (q : Density (Fin e.b))
    (ρ σ A B : Density (Fin e.b)) (p : ℝ) (hp : 0 ≤ p)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) :
    |physicalLinearized β (withSource e ρ) q t-physicalLinearized β (withSource e σ) q t| ≤ 
      2*p*bound β S q := by
  rw [physical_difference β e q ρ σ A B p h t,abs_mul,abs_of_nonneg hp]
  calc _  ≤  p*(|physicalLinearized β (withSource e A) q t|+|physicalLinearized β (withSource e B) q t|) :=
         mul_le_mul_of_nonneg_left (abs_sub _ _) hp
       _  ≤  p*(bound β S q+bound β S q) :=
         mul_le_mul_of_nonneg_left (add_le_add (physical_abs β (withSource e A) q t) (physical_abs β (withSource e B) q t)) hp
       _ = _ := by ring

end ScheduleLaw.Blueprint.SourceFunctional
