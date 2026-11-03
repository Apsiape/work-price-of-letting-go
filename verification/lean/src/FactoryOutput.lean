import FactoryCoding
import FactoryEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryOutput
open History

/-- A subnormalized exact successful output controls the unconditional output,
without any assertion that the failed output or retained residue is independent. -/
theorem dominated_distance {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Density a) (p : ℝ) (hp : p≤1)
    (hgap : (ρ.matrix-(p : ℂ) • σ.matrix).PosSemidef) :
    traceDistance ρ.matrix σ.matrix ≤ 1-p := by
  have hn : Matrix.traceNorm (ρ.matrix-(p : ℂ) • σ.matrix)=1-p := by
    have ht := congrArg Complex.re hgap.traceNorm_eq_trace
    simpa only [Complex.ofReal_re,trace_sub,trace_smul,ρ.normalized,σ.normalized,
      smul_eq_mul,mul_one,Complex.sub_re,Complex.one_re] using ht
  have he : ρ.matrix-σ.matrix =
      (ρ.matrix-(p : ℂ) • σ.matrix)+-((1-p : ℝ) : ℂ) • σ.matrix := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have hb := Matrix.traceNorm_add_le (ρ.matrix-(p : ℂ) • σ.matrix)
    (-((1-p : ℝ) : ℂ) • σ.matrix)
  rw [← he,hn,Matrix.traceNorm_smul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hp),ClassicalFlag.density_traceNorm] at hb
  rw [traceDistance,ClassicalFlag.traceNorm_eq_library]
  linarith

theorem distance_triangle {a : Type} [Fintype a] [DecidableEq a]
    (A B C : Mat a) : traceDistance A C≤traceDistance A B+traceDistance B C := by
  unfold traceDistance
  simp only [ClassicalFlag.traceNorm_eq_library]
  have he : A-C=(A-B)+(B-C) := by abel
  have h := Matrix.traceNorm_add_le (A-B) (B-C)
  rw [← he] at h
  linarith

theorem unconditional_error {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Density a) (target : Mat a) (p ε f : ℝ) (hp : p≤1) (hpf : 1-f≤p)
    (hgap : (ρ.matrix-(p : ℂ) • σ.matrix).PosSemidef)
    (hσ : traceDistance σ.matrix target≤ε) :
    traceDistance ρ.matrix target≤ε+f := by
  have hd := dominated_distance ρ σ p hp hgap
  have ht := distance_triangle ρ.matrix σ.matrix target
  linarith

variable {a c : Type} [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq c]

def branch (ρ : Mat (a × (Fin 2 × c))) (w : Fin 2) : Mat a :=
  partialRight (ρ.submatrix (fun z : a × c => (z.1,w,z.2))
    (fun z : a × c => (z.1,w,z.2)))

omit [DecidableEq a] [DecidableEq c] in
theorem branch_positive (ρ : Mat (a × (Fin 2 × c))) (hρ : ρ.PosSemidef) (w : Fin 2) :
    (branch ρ w).PosSemidef := partialRight_positive (hρ.submatrix _)

omit [Fintype a] [DecidableEq a] [DecidableEq c] in
theorem marginal_split (ρ : Mat (a × (Fin 2 × c))) :
    partialRight ρ=branch ρ 0+branch ρ 1 := by
  ext i j
  simp only [partialRight,branch,Matrix.add_apply,Matrix.submatrix_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two]

theorem marginal_dominates (ρ : Mat (a × (Fin 2 × c))) (hρ : ρ.PosSemidef) :
    (partialRight ρ-branch ρ 1).PosSemidef := by
  rw [marginal_split,add_sub_cancel_right]
  exact branch_positive ρ hρ 0

/-- Exact branch output gives a bound on the complete emitted batch. -/
theorem branch_error (ρ : Density (a × (Fin 2 × c))) (σ : Density a)
    (target : Mat a) (p ε f : ℝ) (hp : p≤1) (hpf : 1-f≤p)
    (hs : branch ρ.matrix 1=(p : ℂ) • σ.matrix)
    (hσ : traceDistance σ.matrix target≤ε) :
    traceDistance (partialRight ρ.matrix) target≤ε+f := by
  let out : Density a := ⟨partialRight ρ.matrix,partialRight_positive ρ.positive,
    by rw [partialRight_trace,ρ.normalized]⟩
  apply unconditional_error out σ target p ε f hp hpf _ hσ
  change (partialRight ρ.matrix-(p : ℂ) • σ.matrix).PosSemidef
  rw [← hs]
  exact marginal_dominates ρ.matrix ρ.positive

end ScheduleLaw.Blueprint.FactoryOutput
