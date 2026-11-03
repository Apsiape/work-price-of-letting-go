import EndpointSchedule
import SourceContraction

/-! Two-sided evolution rules for a wire-kernel induction. Both kernels
may differ, so source-purifier off-diagonal blocks and inserted signed
observables are retained. These are matrix identities, not a hypothesis
asserting the unassembled schedule-wide operational representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

theorem naturality_cross_evolution {a b : Type} [Fintype a] [Fintype b]
    (K L : Matrix b a ℂ) (Tin : Mat a) (Tout : Mat b)
    (hK : K*Tin = Tout*K) (hL : L*Tin = Tout*L) (ρ : Mat a) :
    K * evolve Tin ρ * Lᴴ = evolve Tout (K*ρ*Lᴴ) := by
  unfold evolve
  rw [cross_sandwich_insert,hK,hL]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem arrival_cross_evolution {a b : Type} [Fintype a] [Fintype b]
    (K L P Q : Matrix b a ℂ) (D Tout : Mat b) (Tin W : Mat a)
    (hP : P*W = K) (hQ : Q*W = L)
    (hN : (D*P)*Tin = Tout*(D*P)) (hM : (D*Q)*Tin = Tout*(D*Q)) (ρ : Mat a) :
    (D*P) * evolve (Tin*W) ρ * (D*Q)ᴴ = evolve (Tout*D) (K*ρ*Lᴴ) := by
  have hp : (D*P)*(Tin*W) = (Tout*D)*K := by
    rw [← Matrix.mul_assoc,hN]
    calc Tout*(D*P)*W = (Tout*D)*(P*W) := by simp only [Matrix.mul_assoc]
      _ = (Tout*D)*K := by rw [hP]
  have hq : (D*Q)*(Tin*W) = (Tout*D)*L := by
    rw [← Matrix.mul_assoc,hM]
    calc Tout*(D*Q)*W = (Tout*D)*(Q*W) := by simp only [Matrix.mul_assoc]
      _ = (Tout*D)*L := by rw [hQ]
  unfold evolve
  rw [cross_sandwich_insert,hp,hq]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem release_cross_evolution {a b : Type} [Fintype a] [Fintype b]
    (K L P Q : Matrix b a ℂ) (D Tout : Mat b) (Tin : Mat a)
    (hN : (D*P)*Tin = Tout*(D*P)) (hM : (D*Q)*Tin = Tout*(D*Q)) (ρ : Mat a)
    (hρ : P*ρ*Qᴴ = K*ρ*Lᴴ) :
    (D*P) * evolve Tin ρ * (D*Q)ᴴ = evolve (Tout*D) (K*ρ*Lᴴ) := by
  rw [naturality_cross_evolution _ _ _ _ hN hM]
  have he : (D*P)*ρ*(D*Q)ᴴ = evolve D (P*ρ*Qᴴ) := by
    simp only [evolve,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he,← evolve_mul,hρ]

theorem arrival_kernel_cancellation {b s h c u : Type} [Fintype s] [Fintype h]
    [Fintype c] [Fintype u] [DecidableEq s] [DecidableEq h] [DecidableEq c] [DecidableEq u]
    (K : Matrix (b × h) (PortStock s c × h) ℂ) :
    heldLift (u := u) (arrivalKernel K) * (arrivalPermutation s h c u).permMatrix ℂ =
      unheldLift (u := u) K := by
  have hU := Recorder.permutation_unitary (arrivalPermutation s h c u)
  have hstar : ((arrivalPermutation s h c u).permMatrix ℂ)ᴴ =
      (arrivalPermutation s h c u).permMatrix ℂ := by
    rw [conjTranspose_permMatrix]
    rfl
  have hsquare := hU.2
  rw [hstar] at hsquare
  rw [arrival_kernel_routing,Matrix.mul_assoc,hsquare,Matrix.mul_one]

end ScheduleLaw.History.Wire
