import CachePreparationHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheServiceHistory
open History CacheServiceGates
variable {I : Inventory} {S : Schedule I}
variable {a : Type} [Fintype a] [DecidableEq a]

def globalWires (bare : Extension S) {N : ℕ} (e : Fin N ≃ Fin bare.b × a) (z : ℕ) :
    Fin N × (Payload I × Fin z) ≃ Global bare z × a := wires e _

theorem joint (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N))
    {z : ℕ} (t : Tester S z) (k : Cut S) :
    jointGate (extension bare hN e ρ) t k =
      (jointGate bare t k ⊗ₖ (1 : Mat a)).submatrix
        (globalWires bare e z) (globalWires bare e z) := by
  have hD : liftDeviceObservable (extension bare hN e ρ) z ((extension bare hN e ρ).gate k) =
      (liftDeviceObservable bare z (bare.gate k) ⊗ₖ (1 : Mat a)).submatrix
        (globalWires bare e z) (globalWires bare e z) := by
    ext i j
    simp only [liftDeviceObservable,extension,gate,globalWires,wires,Equiv.coe_fn_mk,
      submatrix_apply,kroneckerMap_apply,Equiv.prodAssoc_symm_apply,one_apply]
    ring
  have hT : liftTesterObservable (extension bare hN e ρ) z (t.gate k) =
      (liftTesterObservable bare z (t.gate k) ⊗ₖ (1 : Mat a)).submatrix
        (globalWires bare e z) (globalWires bare e z) := by
    ext i j
    have hij : i.1=j.1 ↔ e i.1=e j.1 := e.injective.eq_iff.symm
    simp only [liftTesterObservable,submatrix_apply,kroneckerMap_apply,one_apply,
      globalWires,wires,Equiv.coe_fn_mk,extension]
    simp only [hij,Prod.ext_iff]
    split_ifs <;> simp_all
  rw [jointGate_as_product,hD,hT,submatrix_mul_equiv,
    ← mul_kronecker_mul,one_mul,jointGate_as_product]

theorem history (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N))
    {z : ℕ} (t : Tester S z) (n : ℕ) :
    historyUnitary (extension bare hN e ρ) t n =
      (historyUnitary bare t n ⊗ₖ (1 : Mat a)).submatrix
        (globalWires bare e z) (globalWires bare e z) := by
  induction n with
  | zero =>
    simp only [historyUnitary,one_kronecker_one]
    exact (submatrix_one_equiv (globalWires bare e z)).symm
  | succ n ih =>
    by_cases hn : n<2*S.visits+1
    · simp only [historyUnitary,dif_pos hn,ih,joint]
      rw [submatrix_mul_equiv,← mul_kronecker_mul,one_mul]
    · simp only [historyUnitary,dif_neg hn,ih]

theorem run_product (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N)) (σ : Density a)
    (hρ : ρ.matrix=(bare.source.matrix ⊗ₖ σ.matrix).submatrix e e)
    {z : ℕ} (t : Tester S z) (n : ℕ) :
    ScheduleLaw.run (extension bare hN e ρ) t n =
      (ScheduleLaw.run bare t n ⊗ₖ σ.matrix).submatrix
        (globalWires bare e z) (globalWires bare e z) := by
  have hi : initialState (extension bare hN e ρ) t =
      (initialState bare t ⊗ₖ σ.matrix).submatrix
        (globalWires bare e z) (globalWires bare e z) := by
    ext i j
    simp only [initialState,extension,hρ,submatrix_apply,kroneckerMap_apply,
      globalWires,wires,Equiv.coe_fn_mk]
    ring
  induction n with
  | zero => exact hi
  | succ n ih =>
    rw [ScheduleLaw.run,ScheduleLaw.run]
    split_ifs with h
    · rw [ih,joint,evolve_submatrix_equiv (globalWires bare e z),IdleExtension.evolve_idle]
    · exact ih

theorem observer_run (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N)) (σ : Density a)
    (hρ : ρ.matrix=(bare.source.matrix ⊗ₖ σ.matrix).submatrix e e)
    {z : ℕ} (t : Tester S z) (n : ℕ) :
    partialLeft (ScheduleLaw.run (extension bare hN e ρ) t n) =
      partialLeft (ScheduleLaw.run bare t n) := by
  rw [run_product bare hN e ρ σ hρ t n]
  ext i j
  change (∑ k, (ScheduleLaw.run bare t n ⊗ₖ σ.matrix)
    (globalWires bare e z (k,i)) (globalWires bare e z (k,j))) = _
  rw [← Equiv.sum_comp e.symm
    (fun k => (ScheduleLaw.run bare t n ⊗ₖ σ.matrix)
      (globalWires bare e z (k,i)) (globalWires bare e z (k,j)))]
  simp only [Fintype.sum_prod_type,globalWires,wires,Equiv.coe_fn_mk,
    Equiv.apply_symm_apply,kroneckerMap_apply,← Finset.mul_sum]
  have hs : ∑ k, σ.matrix k k=1 := σ.normalized
  simp only [hs,mul_one]
  rfl

theorem handoff (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N)) (σ : Density a)
    (hρ : ρ.matrix=(bare.source.matrix ⊗ₖ σ.matrix).submatrix e e)
    {z : ℕ} (t : Tester S z) :
    ScheduleLaw.handoff (extension bare hN e ρ) t = ScheduleLaw.handoff bare t := by
  unfold ScheduleLaw.handoff
  apply Finset.sum_congr rfl
  intro v _
  simp only [ClassicalFlag.carrierEnergy_reduced,observer_run bare hN e ρ σ hρ]

/-- Every retained register has its exact initial marginal, even when it
is initially correlated with the service source. -/
theorem retained (bare : Extension S) {N : ℕ} (hN : 0<N)
    (e : Fin N ≃ Fin bare.b × a) (ρ : Density (Fin N))
    {z : ℕ} (t : Tester S z) (n : ℕ) :
    partialLeft ((partialRight (ScheduleLaw.run (extension bare hN e ρ) t n)).submatrix e.symm e.symm) =
      partialLeft (ρ.matrix.submatrix e.symm e.symm) := by
  let G := globalWires bare e z
  have hr : (ScheduleLaw.run (extension bare hN e ρ) t n).submatrix G.symm G.symm =
      evolve (historyUnitary bare t n ⊗ₖ (1 : Mat a))
        ((initialState (extension bare hN e ρ) t).submatrix G.symm G.symm) := by
    rw [run_eq_history,← evolve_submatrix_equiv G.symm,history]
    congr 1
    ext i j
    simp only [submatrix_apply,G,Equiv.apply_symm_apply]
  have hh := congrArg partialLeft hr
  rw [partialLeft_evolve_kron_one _ _ (historyUnitary_unitary bare t n)] at hh
  have hi : initialState (extension bare hN e ρ) t=ρ.matrix ⊗ₖ initialTesterMatrix t := rfl
  rw [hi] at hh
  have htr : ∑ o,initialTesterMatrix t o o=1 := initialTesterMatrix_trace t
  ext i j
  have h := congrFun (congrFun hh i) j
  simp only [partialLeft,submatrix_apply,G,globalWires,wires,Equiv.coe_fn_symm_mk,
    Fintype.sum_prod_type,kroneckerMap_apply,← Finset.mul_sum,htr,mul_one] at h
  simpa only [partialLeft,partialRight,submatrix_apply,Fintype.sum_prod_type] using h

end ScheduleLaw.Blueprint.CacheServiceHistory
