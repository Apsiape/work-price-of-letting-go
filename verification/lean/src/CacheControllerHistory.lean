import CacheHardwareHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheControllerHistory
open History
variable {I : Inventory} {S : Schedule I}
variable {a c b : Type} [Fintype a] [Fintype c] [Fintype b]
  [DecidableEq a] [DecidableEq c] [DecidableEq b]
variable (bare : Extension S) {N : ℕ} (e : Fin N ≃ Fin bare.b × a) (A : a ≃ c × b)

def sourceWires : Fin N ≃ c × (Fin bare.b × b) where
  toFun z := let x := e z; let y := A x.2; (y.1,x.1,y.2)
  invFun z := e.symm (z.2.1,A.symm (z.1,z.2.2))
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨i,j,k⟩; simp only [Equiv.apply_symm_apply]

def globalWires (z : ℕ) : Fin N × (Payload I × Fin z) ≃ c × (Global bare z × b) where
  toFun w := let x := e w.1; let y := A x.2; (y.1,(x.1,w.2),y.2)
  invFun w := (e.symm (w.2.1.1,A.symm (w.1,w.2.2)),w.2.1.2)
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨i,⟨j,o⟩,k⟩; simp only [Equiv.apply_symm_apply]

def restWires (z : ℕ) : Global bare z × b ≃ (Fin bare.b × b) × (Payload I × Fin z) where
  toFun w := ((w.1.1,w.2),w.1.2)
  invFun w := ((w.1.1,w.2),w.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem history_framed (hN : 0<N) (ρ : Density (Fin N)) {z : ℕ} (t : Tester S z) (n : ℕ) :
    (historyUnitary (CacheServiceGates.extension bare hN e ρ) t n).submatrix
      (globalWires bare e A z).symm (globalWires bare e A z).symm =
        (1 : Mat c) ⊗ₖ (historyUnitary bare t n ⊗ₖ (1 : Mat b)) := by
  rw [CacheServiceHistory.history]
  ext ⟨ci,gi,bi⟩ ⟨cj,gj,bj⟩
  have he : A.symm (ci,bi)=A.symm (cj,bj) ↔ ci=cj ∧ bi=bj := by
    rw [A.symm.injective.eq_iff]
    exact Prod.ext_iff
  simp only [submatrix_apply,CacheServiceHistory.globalWires,CacheServiceGates.wires,
    globalWires,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,Equiv.apply_symm_apply,
    kroneckerMap_apply,one_apply,he]
  split_ifs <;> simp_all

theorem initial_product (hN : 0<N) (ρ : Density (Fin N)) (C : Density c) (R : Density (Fin bare.b × b))
    (h : ρ.matrix.submatrix (sourceWires bare e A).symm (sourceWires bare e A).symm = C.matrix ⊗ₖ R.matrix)
    {z : ℕ} (t : Tester S z) :
    (initialState (CacheServiceGates.extension bare hN e ρ) t).submatrix
      (globalWires bare e A z).symm (globalWires bare e A z).symm =
        C.matrix ⊗ₖ ((R.matrix ⊗ₖ initialTesterMatrix t).submatrix (restWires bare (b:=b) z) (restWires bare (b:=b) z)) := by
  ext ⟨ci,⟨di,oi⟩,bi⟩ ⟨cj,⟨dj,oj⟩,bj⟩
  have hh := congrFun (congrFun h (ci,di,bi)) (cj,dj,bj)
  simp only [sourceWires,submatrix_apply,Equiv.coe_fn_symm_mk,kroneckerMap_apply] at hh
  change ρ.matrix (e.symm (di,A.symm (ci,bi))) (e.symm (dj,A.symm (cj,bj))) *
    initialTesterMatrix t oi oj = _
  rw [hh]
  simp only [restWires,submatrix_apply,Equiv.coe_fn_mk,kroneckerMap_apply]
  ring

theorem run_product (hN : 0<N) (ρ : Density (Fin N)) (C : Density c) (R : Density (Fin bare.b × b))
    (h : ρ.matrix.submatrix (sourceWires bare e A).symm (sourceWires bare e A).symm = C.matrix ⊗ₖ R.matrix)
    {z : ℕ} (t : Tester S z) (n : ℕ) :
    ∃ σ : Density (Global bare z × b),
      (ScheduleLaw.run (CacheServiceGates.extension bare hN e ρ) t n).submatrix
        (globalWires bare e A z).symm (globalWires bare e A z).symm = C.matrix ⊗ₖ σ.matrix := by
  let D : Density (Global bare z × b) :=
    ⟨(R.matrix ⊗ₖ initialTesterMatrix t).submatrix (restWires bare (b:=b) z) (restWires bare (b:=b) z),
      (R.positive.kronecker (pureMatrix_positive _)).submatrix _,by
        rw [submatrix_trace_equiv,trace_kronecker,R.normalized,initialTesterMatrix_trace,one_mul]⟩
  let V := historyUnitary bare t n ⊗ₖ (1 : Mat b)
  have hv : IsUnitary V := unitary_kron (historyUnitary_unitary bare t n) (by constructor <;> simp)
  let σ : Density (Global bare z × b) :=
    ⟨evolve V D.matrix,(evolve_density V D.matrix hv D.positive D.normalized).1,
      (evolve_density V D.matrix hv D.positive D.normalized).2⟩
  refine ⟨σ,?_⟩
  rw [run_eq_history,← evolve_submatrix_equiv (globalWires bare e A z).symm,
    history_framed bare e A hN ρ t n,initial_product bare e A hN ρ C R h t,
    CacheFlaggedCircuit.kron_evolve]
  simp only [evolve,conjTranspose_one,one_mul,mul_one]
  rfl

theorem contact_product (hN : 0<N) (ρ : Density (Fin N)) (C : Density c) (R : Density (Fin bare.b × b))
    (h : ρ.matrix.submatrix (sourceWires bare e A).symm (sourceWires bare e A).symm = C.matrix ⊗ₖ R.matrix)
    (U : Mat (Fin N)) (hU : IsUnitary U) (V : Mat (Fin bare.b × b)) (hV : IsUnitary V)
    (hu : U.submatrix (sourceWires bare e A).symm (sourceWires bare e A).symm = (1 : Mat c) ⊗ₖ V)
    {z : ℕ} (t : Tester S z) :
    ∃ σ : Density (Global bare z × b),
      (finalState (finalBodyContact (CacheServiceGates.extension bare hN e ρ) U hU) t).submatrix
        (globalWires bare e A z).symm (globalWires bare e A z).symm = C.matrix ⊗ₖ σ.matrix := by
  obtain ⟨σ0,hσ0⟩ := run_product bare e A hN ρ C R h t (2*S.visits+1)
  let Vg := (V ⊗ₖ (1 : Mat (Payload I × Fin z))).submatrix
    (restWires bare (b:=b) z) (restWires bare (b:=b) z)
  have hvg : IsUnitary Vg := unitary_submatrix _ (unitary_kron hV (by constructor <;> simp))
  have hg : (U ⊗ₖ (1 : Mat (Payload I × Fin z))).submatrix
      (globalWires bare e A z).symm (globalWires bare e A z).symm = (1 : Mat c) ⊗ₖ Vg := by
    ext ⟨ci,⟨di,oi⟩,bi⟩ ⟨cj,⟨dj,oj⟩,bj⟩
    have hh := congrFun (congrFun hu (ci,di,bi)) (cj,dj,bj)
    simp only [sourceWires,submatrix_apply,Equiv.coe_fn_symm_mk,kroneckerMap_apply] at hh
    simp only [globalWires,submatrix_apply,Equiv.coe_fn_symm_mk,kroneckerMap_apply]
    rw [hh]
    simp only [Vg,restWires,submatrix_apply,Equiv.coe_fn_mk,kroneckerMap_apply]
    ring
  let σ : Density (Global bare z × b) :=
    ⟨evolve Vg σ0.matrix,(evolve_density Vg σ0.matrix hvg σ0.positive σ0.normalized).1,
      (evolve_density Vg σ0.matrix hvg σ0.positive σ0.normalized).2⟩
  refine ⟨σ,?_⟩
  rw [finalBodyContact_finalState,← evolve_submatrix_equiv (globalWires bare e A z).symm,hg]
  change evolve ((1 : Mat c) ⊗ₖ Vg)
    ((ScheduleLaw.run (CacheServiceGates.extension bare hN e ρ) t (2*S.visits+1)).submatrix
      (globalWires bare e A z).symm (globalWires bare e A z).symm) = _
  rw [hσ0,CacheFlaggedCircuit.kron_evolve]
  simp only [evolve,conjTranspose_one,one_mul,mul_one]
  rfl

end ScheduleLaw.Blueprint.CacheControllerHistory
