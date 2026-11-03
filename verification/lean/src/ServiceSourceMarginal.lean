import CacheServiceHistory
import SourceFunctional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.ServiceSourceMarginal
open History CacheServiceHistory
variable {I : Inventory} {S : Schedule I}
variable {a : Type} [Fintype a] [DecidableEq a]
variable (bare : Extension S) {N : ℕ} (e : Fin N ≃ Fin bare.b × a)

def source (ρ : Density (Fin N)) : Density (Fin bare.b) :=
  ⟨partialRight (ρ.matrix.submatrix e.symm e.symm),
    partialRight_positive (ρ.positive.submatrix _),by
      rw [partialRight_trace,submatrix_trace_equiv,ρ.normalized]⟩

theorem run_marginal (hN : 0<N) (ρ : Density (Fin N))
    {z : ℕ} (t : Tester S z) (k : ℕ) :
    partialRight ((ScheduleLaw.run (CacheServiceGates.extension bare hN e ρ) t k).submatrix
      (globalWires bare e z).symm (globalWires bare e z).symm)=
        ScheduleLaw.run (CacheSourceHistory.withSource bare (source bare e ρ)) t k := by
  let G := globalWires bare e z
  have hr : (ScheduleLaw.run (CacheServiceGates.extension bare hN e ρ) t k).submatrix G.symm G.symm =
      evolve (historyUnitary bare t k ⊗ₖ (1 : Mat a))
        ((initialState (CacheServiceGates.extension bare hN e ρ) t).submatrix G.symm G.symm) := by
    rw [run_eq_history,← evolve_submatrix_equiv G.symm,CacheServiceHistory.history]
    congr 1
    ext i j
    simp only [submatrix_apply,G,Equiv.apply_symm_apply]
  rw [hr,partialRight_evolve_kron_one,CacheSourceHistory.run]
  congr 1
  ext ⟨i,o⟩ ⟨j,o'⟩
  simp only [partialRight,initialState,CacheServiceGates.extension,submatrix_apply,
    G,globalWires,CacheServiceGates.wires,Equiv.coe_fn_symm_mk,kroneckerMap_apply,
    source,Finset.sum_mul,initialTesterMatrix]

theorem observer_run (hN : 0<N) (ρ : Density (Fin N))
    {z : ℕ} (t : Tester S z) (k : ℕ) :
    partialLeft (ScheduleLaw.run (CacheServiceGates.extension bare hN e ρ) t k)=
      partialLeft (ScheduleLaw.run (CacheSourceHistory.withSource bare (source bare e ρ)) t k) := by
  rw [← run_marginal bare e hN ρ t k]
  ext i j
  simp only [partialLeft,partialRight,submatrix_apply,globalWires,CacheServiceGates.wires,
    Equiv.coe_fn_symm_mk]
  simpa only [Fintype.sum_prod_type] using
    (Equiv.sum_comp e.symm (fun u : Fin N =>
      (ScheduleLaw.run (CacheServiceGates.extension bare hN e ρ) t k) (u,i) (u,j))).symm

theorem handoff (hN : 0<N) (ρ : Density (Fin N)) {z : ℕ} (t : Tester S z) :
    ScheduleLaw.handoff (CacheServiceGates.extension bare hN e ρ) t=
      ScheduleLaw.handoff (CacheSourceHistory.withSource bare (source bare e ρ)) t := by
  unfold ScheduleLaw.handoff
  apply Finset.sum_congr rfl
  intro v _
  simp only [ClassicalFlag.carrierEnergy_reduced,observer_run bare e hN ρ]

theorem body (hN : 0<N) (ρ : Density (Fin N)) {z : ℕ} (t : Tester S z) :
    partialRight ((bodyOutput (CacheServiceGates.extension bare hN e ρ) t).submatrix e.symm e.symm)=
      bodyOutput (CacheSourceHistory.withSource bare (source bare e ρ)) t := by
  simp only [bodyOutput,finalState]
  rw [← run_marginal bare e hN ρ t (2*S.visits+1)]
  ext i j
  simp only [partialRight,submatrix_apply,finalState,globalWires,CacheServiceGates.wires,
    Equiv.coe_fn_symm_mk]
  exact Finset.sum_comm

end ScheduleLaw.Blueprint.ServiceSourceMarginal
