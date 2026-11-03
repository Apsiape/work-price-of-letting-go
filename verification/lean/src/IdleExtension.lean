import FlagAccounting

/-! Counted idle finite stock, including its explicit inert purification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace IdleExtension

/-- Reorder a body product so the live circuit stays next to its payload. -/
def wires (a b : ℕ) (p : Type) : Fin (a*b) × p ≃ (Fin a × p) × Fin b where
  toFun x := (((finProdFinEquiv.symm x.1).1,x.2),(finProdFinEquiv.symm x.1).2)
  invFun x := (finProdFinEquiv (x.1.1,x.2),x.1.2)
  left_inv x := by
    change (finProdFinEquiv (finProdFinEquiv.symm x.1),x.2) = x
    rw [Equiv.apply_symm_apply]
  right_inv x := by
    change (((finProdFinEquiv.symm (finProdFinEquiv (x.1.1,x.2))).1,x.1.2),
      (finProdFinEquiv.symm (finProdFinEquiv (x.1.1,x.2))).2) = x
    rw [Equiv.symm_apply_apply]

def purifierWires (a b f g : ℕ) :
    Fin (a*b) × Fin (f*g) ≃ (Fin a × Fin f) × (Fin b × Fin g) :=
  (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    (Equiv.prodProdProdComm _ _ _ _)

def source {I : Inventory} {S : Schedule I} (e q : Extension S) :
    Density (Fin (e.b*q.b)) where
  matrix := (e.source.matrix ⊗ₖ q.source.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  positive := (positive_kron e.source.positive q.source.positive).submatrix _
  normalized := by rw [submatrix_trace_equiv,trace_kronecker,e.source.normalized,q.source.normalized,one_mul]

def purification {I : Inventory} {S : Schedule I} (e q : Extension S) :
    Fin (e.b*q.b) × Fin (e.f*q.f) → ℂ :=
  fun x => e.purification (purifierWires e.b q.b e.f q.f x).1 *
    q.purification (purifierWires e.b q.b e.f q.f x).2

theorem purification_normalized {I : Inventory} {S : Schedule I} (e q : Extension S) :
    ∑ x, Complex.normSq (purification e q x) = 1 := by
  change (∑ x, Complex.normSq
    (e.purification (purifierWires e.b q.b e.f q.f x).1 *
      q.purification (purifierWires e.b q.b e.f q.f x).2)) = _
  rw [Equiv.sum_comp (purifierWires e.b q.b e.f q.f)
    (fun x => Complex.normSq (e.purification x.1 * q.purification x.2))]
  simp only [Fintype.sum_prod_type,map_mul,← Finset.mul_sum,← Finset.sum_mul,
    e.purification_norm,q.purification_norm,mul_one]

theorem purification_reduces {I : Inventory} {S : Schedule I} (e q : Extension S) :
    partialRight (pureMatrix (purification e q)) = (source e q).matrix := by
  ext i j
  obtain ⟨i,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finProdFinEquiv.surjective j
  change (∑ k, pureMatrix (purification e q) (finProdFinEquiv i,k) (finProdFinEquiv j,k)) = _
  rw [← Equiv.sum_comp finProdFinEquiv
    (fun k => pureMatrix (purification e q) (finProdFinEquiv i,k) (finProdFinEquiv j,k))]
  simp only [Fintype.sum_prod_type,pureMatrix,purification,purifierWires,
    Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map,Equiv.symm_apply_apply,
    Equiv.prodProdProdComm_apply,star_mul]
  have he := congrFun (congrFun e.purification_reduces i.1) j.1
  have hq := congrFun (congrFun q.purification_reduces i.2) j.2
  simp only [partialRight,pureMatrix] at he hq
  change (∑ k, ∑ l, e.purification (i.1,k) * q.purification (i.2,l) *
    (star (q.purification (j.2,l)) * star (e.purification (j.1,k)))) = _
  calc _ = (∑ k, e.purification (i.1,k) * star (e.purification (j.1,k))) *
      (∑ l, q.purification (i.2,l) * star (q.purification (j.2,l))) := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
    _ = _ := by rw [he,hq]; simp [source,kroneckerMap_apply]

def gate {I : Inventory} {S : Schedule I} (e q : Extension S) (k : Cut S) :
    Mat (Fin (e.b*q.b) × Payload I) :=
  (e.gate k ⊗ₖ (1 : Mat (Fin q.b))).submatrix (wires e.b q.b _) (wires e.b q.b _)

theorem gate_unitary {I : Inventory} {S : Schedule I} (e q : Extension S) (k : Cut S) :
    IsUnitary (gate e q k) :=
  unitary_submatrix _ (unitary_kron (e.unitary k) (by constructor <;> simp))

theorem gate_local {I : Inventory} {S : Schedule I} (e q : Extension S) (k : Cut S) :
    LocalOn I (e.b*q.b) (held S k) (gate e q k) := by
  obtain ⟨U,hU,he⟩ := e.gate_local k
  refine ⟨(U ⊗ₖ (1 : Mat (Fin q.b))).submatrix (wires e.b q.b _) (wires e.b q.b _),
    unitary_submatrix _ (unitary_kron hU (by constructor <;> simp)),?_⟩
  intro i j
  simp only [gate,wires,Equiv.coe_fn_mk,submatrix_apply,kroneckerMap_apply,he,one_apply]
  ring

/-- Only the preparation fields of q are used; none of its contact gates runs. -/
def extension {I : Inventory} {S : Schedule I} (e q : Extension S) : Extension S where
  b := e.b*q.b
  b_pos := Nat.mul_pos e.b_pos q.b_pos
  source := source e q
  f := e.f*q.f
  f_pos := Nat.mul_pos e.f_pos q.f_pos
  purification := purification e q
  purification_norm := purification_normalized e q
  purification_reduces := purification_reduces e q
  gate := gate e q
  unitary := gate_unitary e q
  gate_local := gate_local e q

def globalWires {I : Inventory} {S : Schedule I} (e q : Extension S) (r : ℕ) :
    Global (extension e q) r ≃ Global e r × Fin q.b := wires e.b q.b _

theorem initialState_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) :
    initialState (extension e q) t = (initialState e t ⊗ₖ q.source.matrix).submatrix
      (globalWires e q r) (globalWires e q r) := by
  ext i j
  simp [initialState,extension,source,globalWires,wires,kroneckerMap_apply]
  ring

theorem liftDevice_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    (r : ℕ) (k : Cut S) :
    liftDeviceObservable (extension e q) r ((extension e q).gate k) =
      (liftDeviceObservable e r (e.gate k) ⊗ₖ (1 : Mat (Fin q.b))).submatrix
        (globalWires e q r) (globalWires e q r) := by
  ext i j
  simp [liftDeviceObservable,extension,gate,globalWires,wires,kroneckerMap_apply,
    Equiv.prodAssoc_symm_apply]
  ring

theorem liftTester_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    (r : ℕ) (U : Mat (Fin r × Payload I)) :
    liftTesterObservable (extension e q) r U =
      (liftTesterObservable e r U ⊗ₖ (1 : Mat (Fin q.b))).submatrix
        (globalWires e q r) (globalWires e q r) := by
  ext i j
  have hij : i.1 = j.1 ↔ (finProdFinEquiv.symm i.1) = (finProdFinEquiv.symm j.1) :=
    finProdFinEquiv.symm.injective.eq_iff.symm
  simp only [liftTesterObservable,submatrix_apply,kroneckerMap_apply,one_apply,
    globalWires,wires]
  simp only [hij,Prod.ext_iff]
  split_ifs <;> simp_all

theorem jointGate_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) (k : Cut S) :
    jointGate (extension e q) t k =
      (jointGate e t k ⊗ₖ (1 : Mat (Fin q.b))).submatrix
        (globalWires e q r) (globalWires e q r) := by
  rw [jointGate_as_product,liftDevice_idle,liftTester_idle,submatrix_mul_equiv,
    ← mul_kronecker_mul,one_mul,jointGate_as_product]

theorem evolve_idle {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (U ρ : Mat a) (σ : Mat b) :
    evolve (U ⊗ₖ (1 : Mat b)) (ρ ⊗ₖ σ) = evolve U ρ ⊗ₖ σ := by
  simp [evolve,conjTranspose_kronecker,← mul_kronecker_mul]

theorem run_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) :
    run (extension e q) t n = (run e t n ⊗ₖ q.source.matrix).submatrix
      (globalWires e q r) (globalWires e q r) := by
  induction n with
  | zero => exact initialState_idle e q t
  | succ n ih =>
    rw [run,run]
    split_ifs with h
    · rw [ih,jointGate_idle,evolve_submatrix_equiv (globalWires e q r),evolve_idle]
    · exact ih

theorem partialLeft_idle {a b : ℕ} {p : Type} [Fintype p]
    (A : Mat (Fin a × p)) (σ : Density (Fin b)) :
    partialLeft ((A ⊗ₖ σ.matrix).submatrix (wires a b p) (wires a b p)) = partialLeft A := by
  ext i j
  change (∑ k, (A ⊗ₖ σ.matrix) (wires a b p (k,i)) (wires a b p (k,j))) = _
  rw [← Equiv.sum_comp finProdFinEquiv
    (fun k => (A ⊗ₖ σ.matrix) (wires a b p (k,i)) (wires a b p (k,j)))]
  simp only [Fintype.sum_prod_type,wires,Equiv.coe_fn_mk,Equiv.symm_apply_apply,kroneckerMap_apply,
    ← Finset.mul_sum]
  have hs : ∑ k, σ.matrix k k = 1 := σ.normalized
  simp only [hs,mul_one]
  rfl

theorem partialRight_idle {a b : ℕ} {p : Type} [Fintype p]
    (A : Mat (Fin a × p)) (σ : Mat (Fin b)) :
    partialRight ((A ⊗ₖ σ).submatrix (wires a b p) (wires a b p)) =
      (partialRight A ⊗ₖ σ).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  simp [partialRight,wires,kroneckerMap_apply,Finset.sum_mul]

theorem observerRun_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) :
    partialLeft (run (extension e q) t n) = partialLeft (run e t n) := by
  rw [run_idle]
  exact partialLeft_idle _ q.source

theorem observerOutput_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) : observerOutput (extension e q) t = observerOutput e t :=
  observerRun_idle e q t (2*S.visits+1)

theorem bodyOutput_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) :
    bodyOutput (extension e q) t = (bodyOutput e t ⊗ₖ q.source.matrix).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  unfold bodyOutput finalState
  rw [run_idle]
  exact partialRight_idle _ q.source.matrix

theorem handoff_idle {I : Inventory} {S : Schedule I} (e q : Extension S)
    {r : ℕ} (t : Tester S r) : handoff (extension e q) t = handoff e t := by
  unfold handoff
  apply Finset.sum_congr rfl
  intro v _
  simp only [ClassicalFlag.carrierEnergy_reduced,observerRun_idle]

theorem score_idle {I : Inventory} {S : Schedule I} (β : ℝ) (e q : Extension S)
    {r : ℕ} (t : Tester S r) : score β (extension e q) t = score β e t := by
  let ρ : Density (Fin e.b) := ⟨bodyOutput e t,(bodyOutput_density e t).1,(bodyOutput_density e t).2⟩
  unfold score
  rw [handoff_idle,bodyOutput_idle]
  change (entropy ((ρ.matrix ⊗ₖ q.source.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm) -
    entropy ((e.source.matrix ⊗ₖ q.source.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)) / β + _ = _
  rw [entropy_submatrix_equiv _ _ (positive_kron ρ.positive q.source.positive).isHermitian,
    entropy_submatrix_equiv _ _ (positive_kron e.source.positive q.source.positive).isHermitian,
    entropy_density_product,entropy_density_product]
  ring

end IdleExtension
end ScheduleLaw
