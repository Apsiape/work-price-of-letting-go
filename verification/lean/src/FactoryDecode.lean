import FactoryOutput
import FiniteTensorMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryDecode
open History

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def output (V : Mat (a × b)) (hV : IsUnitary V) (ρ : Density (a × b)) : Density a :=
  ⟨partialRight (evolve V ρ.matrix),
    partialRight_positive (ρ.positive.mul_mul_conjTranspose_same V),by
      rw [partialRight_trace,evolve_trace _ _ hV,ρ.normalized]⟩

theorem dominated (V : Mat (a × b)) (ρ σ : Mat (a × b)) (p : ℝ)
    (hgap : (ρ-(p : ℂ) • σ).PosSemidef) :
    (partialRight (evolve V ρ)-(p : ℂ) • partialRight (evolve V σ)).PosSemidef := by
  have h := partialRight_positive (hgap.mul_mul_conjTranspose_same V)
  change (partialRight (evolve V (ρ-(p : ℂ) • σ))).PosSemidef at h
  have he : partialRight (evolve V (ρ-(p : ℂ) • σ)) =
      partialRight (evolve V ρ)-(p : ℂ) • partialRight (evolve V σ) := by
    unfold evolve
    rw [mul_sub,sub_mul,Matrix.mul_smul,smul_mul_assoc]
    ext i j
    simp only [partialRight,Matrix.sub_apply,Matrix.smul_apply,
      Finset.sum_sub_distrib,smul_eq_mul,Finset.mul_sum]
  rwa [he] at h

/-- Decode and discard the literal residue only after proving the positive
operator comparison for the full retained state. -/
theorem error (V : Mat (a × b)) (hV : IsUnitary V) (ρ σ : Density (a × b))
    (target : Mat a) (p ε f : ℝ) (hp : p≤1) (hpf : 1-f≤p)
    (hgap : (ρ.matrix-(p : ℂ) • σ.matrix).PosSemidef)
    (hσ : traceDistance (partialRight (evolve V σ.matrix)) target≤ε) :
    traceDistance (partialRight (evolve V ρ.matrix)) target≤ε+f :=
  FactoryOutput.unconditional_error (output V hV ρ) (output V hV σ) target p ε f
    hp hpf (dominated V ρ.matrix σ.matrix p hgap) hσ

end ScheduleLaw.Blueprint.FactoryDecode
