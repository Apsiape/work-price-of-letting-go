import CacheRareProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheSourceHistory
open History

variable {I : Inventory} {S : Schedule I}

abbrev withSource (e : Extension S) (ρ : Density (Fin e.b)) : Extension S where
  b := e.b
  b_pos := e.b_pos
  source := ρ
  f := e.b
  f_pos := e.b_pos
  purification := ρ.toMState.purify.vec
  purification_norm := by
    simpa only [Complex.normSq_eq_norm_sq,Ket.coe_fun_eq] using ρ.toMState.purify.normalized
  purification_reduces := density_purification_matrix ρ.toMState
  gate := e.gate
  unitary := e.unitary
  gate_local := e.gate_local

theorem history (e : Extension S) (ρ : Density (Fin e.b)) {z : ℕ} (t : Tester S z) (n : ℕ) :
    historyUnitary (withSource e ρ) t n=historyUnitary e t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n<2*S.visits+1
    · simp only [historyUnitary,dif_pos hn,ih]
      rfl
    · simp only [historyUnitary,dif_neg hn,ih]

theorem run (e : Extension S) (ρ : Density (Fin e.b)) {z : ℕ} (t : Tester S z) (n : ℕ) :
    (ScheduleLaw.run (withSource e ρ) t n : Mat (Global e z)) =
      evolve (historyUnitary e t n) (ρ.matrix ⊗ₖ initialTesterMatrix t) := by
  rw [run_eq_history,history]
  rfl

theorem difference (e : Extension S) (ρ σ A B : Density (Fin e.b)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) (n : ℕ) :
    (ScheduleLaw.run (withSource e ρ) t n : Mat (Global e z))-(ScheduleLaw.run (withSource e σ) t n : Mat (Global e z)) =
      p • ((ScheduleLaw.run (withSource e A) t n : Mat (Global e z))-(ScheduleLaw.run (withSource e B) t n : Mat (Global e z))) := by
  rw [run,run,run,run]
  have hh := congrArg (fun M => evolve (historyUnitary e t n) (M ⊗ₖ initialTesterMatrix t)) h
  simpa only [CacheRareProduct.sub_kron,smul_kronecker,evolve,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul] using hh

theorem observer_difference (e : Extension S) (ρ σ A B : Density (Fin e.b)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) {z : ℕ} (t : Tester S z) :
    observerOutput (withSource e ρ) t-observerOutput (withSource e σ) t =
      p • (observerOutput (withSource e A) t-observerOutput (withSource e B) t) := by
  have hh := congrArg (fun M : Mat (Global e z) => partialLeft M) (difference e ρ σ A B p h t (2*S.visits+1))
  ext i j
  have he := congrFun (congrFun hh i) j
  simpa only [observerOutput,finalState,partialLeft,Matrix.sub_apply,Matrix.smul_apply,
    Finset.sum_sub_distrib,← Finset.smul_sum] using he

/-- Uniform service control for every coherent tester follows from the
literal rare-branch source difference, without a tester-dimension bound. -/
theorem approximates (e : Extension S) (ρ σ A B : Density (Fin e.b)) (p : ℝ) (hp : 0≤p)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) :
    Approximates (withSource e ρ) (withSource e σ) p := by
  intro z t
  let U : Density (Payload I × Fin z) :=
    ⟨observerOutput (withSource e A) t,partialLeft_positive (run_density (withSource e A) t _).1,
      by rw [observerOutput,partialLeft_trace]; exact (run_density (withSource e A) t _).2⟩
  let V : Density (Payload I × Fin z) :=
    ⟨observerOutput (withSource e B) t,partialLeft_positive (run_density (withSource e B) t _).1,
      by rw [observerOutput,partialLeft_trace]; exact (run_density (withSource e B) t _).2⟩
  exact CacheRareProduct.distance_of_difference _ _ U V p hp (observer_difference e ρ σ A B p h t)

end ScheduleLaw.Blueprint.CacheSourceHistory
