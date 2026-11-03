import CircuitEnergy
import EntropyProducts
import QuantumEntropyAdapter

/-! Orthogonally flagged finite circuits, with the flag purification retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace ClassicalFlag

def block {a b : Type} (A : Mat a) (B : Mat b) : Mat (a ⊕ b) :=
  fromBlocks A 0 0 B

theorem block_unitary {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (A : Mat a) (B : Mat b)
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (block A B) := by
  constructor <;>
    simp [block,fromBlocks_conjTranspose,fromBlocks_multiply,hA.1,hA.2,hB.1,hB.2,
      ← fromBlocks_one]

theorem block_hermitian {a b : Type} (A : Mat a) (B : Mat b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (block A B).IsHermitian :=
  hA.fromBlocks (by simp) hB

theorem block_trace {a b : Type} [Fintype a] [Fintype b] (A : Mat a) (B : Mat b) :
    (block A B).trace = A.trace + B.trace := by
  simp [trace,block,Fintype.sum_sum_type]

theorem block_evolve {a b : Type} [Fintype a] [Fintype b]
    (U A : Mat a) (V B : Mat b) :
    evolve (block U V) (block A B) = block (evolve U A) (evolve V B) := by
  simp [evolve,block,fromBlocks_multiply,fromBlocks_conjTranspose]

theorem block_entropy {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (A : Mat a) (B : Mat b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    entropy (block A B) = entropy A + entropy B := by
  rw [entropy_eq_charpoly_roots _ (block_hermitian A B hA hB),
    entropy_eq_charpoly_roots _ hA,entropy_eq_charpoly_roots _ hB]
  simp only [block,charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul (mul_ne_zero (charpoly_monic A).ne_zero (charpoly_monic B).ne_zero),
    Multiset.map_add,Multiset.sum_add]

theorem entropy_weight {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Density a) (p : ℝ) (hp : 0 ≤ p) :
    entropy ((p : ℂ) • ρ.matrix) = Real.negMulLog p + p * entropy ρ.matrix := by
  let U : Mat a := ρ.positive.isHermitian.eigenvectorUnitary
  let D : Mat a := diagonal (fun i => ((p * ρ.positive.isHermitian.eigenvalues i : ℝ) : ℂ))
  have hU : IsUnitary U :=
    ⟨ρ.positive.isHermitian.eigenvectorUnitary.2.1,
      ρ.positive.isHermitian.eigenvectorUnitary.2.2⟩
  have hD : D.PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i
    exact Complex.nonneg_iff.mpr ⟨mul_nonneg hp (ρ.positive.eigenvalues_nonneg i),rfl⟩
  have he : (p : ℂ) • ρ.matrix = evolve U D := by
    rw [ρ.positive.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply,star_eq_conjTranspose,evolve,U,D]
    rw [← smul_mul_assoc,← Matrix.mul_smul,← diagonal_smul]
    congr 2
    ext i
    simp [Complex.ofReal_mul,diagonal_apply]
  rw [he,entropy_unitary_evolve U D hU hD,entropy_diagonal_real]
  simp_rw [negMulLog_mul_nonnegative hp (ρ.positive.eigenvalues_nonneg _),
    Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  rw [density_eigenvalues_sum ρ,one_mul,entropy_of_hermitian _ ρ.positive.isHermitian]

def vector {I : Inventory} {S : Schedule I} (e f : Extension S) (δ : ℝ) :
    (Fin e.b ⊕ Fin f.b) × (Fin e.f ⊕ Fin f.f) → ℂ
  | (Sum.inl i,Sum.inl j) => (Real.sqrt (1-δ) : ℂ) * e.purification (i,j)
  | (Sum.inr i,Sum.inr j) => (Real.sqrt δ : ℂ) * f.purification (i,j)
  | _ => 0

theorem vector_normalized {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∑ x, Complex.normSq (vector e f δ x) = 1 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,vector,map_mul,
    Complex.normSq_ofReal,Real.mul_self_sqrt (sub_nonneg.mpr hδ1),
    Real.mul_self_sqrt hδ,Complex.normSq_zero,Finset.sum_const_zero,add_zero,zero_add,
    ← Finset.mul_sum]
  have he := e.purification_norm
  have hf := f.purification_norm
  simp only [Fintype.sum_prod_type] at he hf
  rw [he,hf]
  ring

theorem vector_reduces {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    partialRight (pureMatrix (vector e f δ)) =
      block (((1-δ : ℝ) : ℂ) • e.source.matrix) ((δ : ℂ) • f.source.matrix) := by
  have he := e.purification_reduces
  have hf := f.purification_reduces
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij := congrFun (congrFun he i) j
      simp only [partialRight,pureMatrix] at hij
      simp only [partialRight,pureMatrix,Fintype.sum_sum_type,vector,block,
        fromBlocks_apply₁₁,smul_apply,smul_eq_mul,star_mul,star_zero,mul_zero,zero_mul,
        Finset.sum_const_zero,add_zero]
      rw [← hij,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hs : (Real.sqrt (1-δ) : ℂ) * star (Real.sqrt (1-δ) : ℂ) = (1-δ : ℝ) := by
        simpa using congrArg (fun r : ℝ => (r : ℂ))
          (Real.mul_self_sqrt (sub_nonneg.mpr hδ1))
      calc _ = ((Real.sqrt (1-δ) : ℂ) * star (Real.sqrt (1-δ) : ℂ)) *
          (e.purification (i,k) * star (e.purification (j,k))) := by ring
        _ = _ := by rw [hs]
    | inr j => simp [partialRight,pureMatrix,Fintype.sum_sum_type,vector,block]
  | inr i =>
    cases j with
    | inl j => simp [partialRight,pureMatrix,Fintype.sum_sum_type,vector,block]
    | inr j =>
      have hij := congrFun (congrFun hf i) j
      simp only [partialRight,pureMatrix] at hij
      simp only [partialRight,pureMatrix,Fintype.sum_sum_type,vector,block,
        fromBlocks_apply₂₂,smul_apply,smul_eq_mul,star_mul,star_zero,zero_mul,mul_zero,
        Finset.sum_const_zero,zero_add]
      rw [← hij,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hs : (Real.sqrt δ : ℂ) * star (Real.sqrt δ : ℂ) = δ := by
        simpa using congrArg (fun r : ℝ => (r : ℂ)) (Real.mul_self_sqrt hδ)
      calc _ = ((Real.sqrt δ : ℂ) * star (Real.sqrt δ : ℂ)) *
          (f.purification (i,k) * star (f.purification (j,k))) := by ring
        _ = _ := by rw [hs]

/-- Distribution of a finite retained flag past a payload factor. -/
def split (a b : ℕ) (p : Type) :
    Fin (a+b) × p ≃ (Fin a × p) ⊕ (Fin b × p) :=
  (Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl p)).trans
    (Equiv.sumProdDistrib (Fin a) (Fin b) p)

def source {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : Density (Fin (e.b+f.b)) where
  matrix := (block (((1-δ : ℝ) : ℂ) • e.source.matrix)
    ((δ : ℂ) • f.source.matrix)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  positive := by
    rw [← vector_reduces e f δ hδ hδ1]
    exact (partialRight_positive (pureMatrix_positive _)).submatrix _
  normalized := by
    rw [submatrix_trace_equiv,block_trace,trace_smul,trace_smul,
      e.source.normalized,f.source.normalized]
    simp

def gate {I : Inventory} {S : Schedule I} (e f : Extension S) (k : Cut S) :
    Mat (Fin (e.b+f.b) × Payload I) :=
  (block (e.gate k) (f.gate k)).submatrix (split e.b f.b (Payload I)) (split e.b f.b (Payload I))

theorem gate_unitary {I : Inventory} {S : Schedule I} (e f : Extension S) (k : Cut S) :
    IsUnitary (gate e f k) :=
  unitary_submatrix _ (block_unitary _ _ (e.unitary k) (f.unitary k))

theorem gate_local {I : Inventory} {S : Schedule I} (e f : Extension S) (k : Cut S) :
    LocalOn I (e.b+f.b) (held S k) (gate e f k) := by
  obtain ⟨U,hU,he⟩ := e.gate_local k
  obtain ⟨V,hV,hf⟩ := f.gate_local k
  refine ⟨(block U V).submatrix (split e.b f.b _) (split e.b f.b _),
    unitary_submatrix _ (block_unitary _ _ hU hV),?_⟩
  intro i j
  obtain ⟨i,pi⟩ := i
  obtain ⟨j,pj⟩ := j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [gate,split,block,he,hf]

def extension {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : Extension S where
  b := e.b+f.b
  b_pos := by have := e.b_pos; omega
  source := source e f δ hδ hδ1
  f := e.f+f.f
  f_pos := by have := e.f_pos; omega
  purification := fun x => vector e f δ (finSumFinEquiv.symm x.1,finSumFinEquiv.symm x.2)
  purification_norm := by
    exact (Equiv.sum_comp (Equiv.prodCongr finSumFinEquiv.symm finSumFinEquiv.symm)
      (fun x => Complex.normSq (vector e f δ x))).trans (vector_normalized e f δ hδ hδ1)
  purification_reduces := by
    ext i j
    have he := congrFun (congrFun (vector_reduces e f δ hδ hδ1)
      (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
    change (∑ k, vector e f δ (finSumFinEquiv.symm i,finSumFinEquiv.symm k) *
      star (vector e f δ (finSumFinEquiv.symm j,finSumFinEquiv.symm k))) = _
    rw [Equiv.sum_comp finSumFinEquiv.symm
      (fun k => vector e f δ (finSumFinEquiv.symm i,k) *
        star (vector e f δ (finSumFinEquiv.symm j,k)))]
    exact he
  gate := gate e f
  unitary := gate_unitary e f
  gate_local := gate_local e f

theorem initialState_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) :
    initialState (extension e f δ hδ hδ1) t =
      (block (((1-δ : ℝ) : ℂ) • initialState e t)
        ((δ : ℂ) • initialState f t)).submatrix
          (split e.b f.b (Payload I × Fin r)) (split e.b f.b (Payload I × Fin r)) := by
  ext i j
  obtain ⟨i,x⟩ := i
  obtain ⟨j,y⟩ := j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [initialState,extension,source,block,split,kroneckerMap_apply,mul_assoc]

theorem liftDevice_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ) (k : Cut S) :
    liftDeviceObservable (extension e f δ hδ hδ1) r ((extension e f δ hδ hδ1).gate k) =
      (block (liftDeviceObservable e r (e.gate k))
        (liftDeviceObservable f r (f.gate k))).submatrix
          (split e.b f.b (Payload I × Fin r)) (split e.b f.b (Payload I × Fin r)) := by
  ext i j
  obtain ⟨i,x⟩ := i
  obtain ⟨j,y⟩ := j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [liftDeviceObservable,extension,gate,block,split,kroneckerMap_apply,
      Equiv.prodAssoc_symm_apply]

theorem liftTester_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ)
    (U : Mat (Fin r × Payload I)) :
    liftTesterObservable (extension e f δ hδ hδ1) r U =
      (block (liftTesterObservable e r U) (liftTesterObservable f r U)).submatrix
        (split e.b f.b (Payload I × Fin r)) (split e.b f.b (Payload I × Fin r)) := by
  have hcross : ∀ i : Fin e.b, ∀ j : Fin f.b, Fin.castAdd f.b i ≠ Fin.natAdd e.b j := by
    intro i j h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    have := i.isLt
    omega
  ext i j
  obtain ⟨i,x⟩ := i
  obtain ⟨j,y⟩ := j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [liftTesterObservable,extension,block,split,kroneckerMap_apply,one_apply,
      hcross,fun i j => Ne.symm (hcross j i)]

theorem jointGate_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) (k : Cut S) :
    jointGate (extension e f δ hδ hδ1) t k =
      (block (jointGate e t k) (jointGate f t k)).submatrix
        (split e.b f.b (Payload I × Fin r)) (split e.b f.b (Payload I × Fin r)) := by
  rw [jointGate_as_product,liftDevice_branches,liftTester_branches,submatrix_mul_equiv]
  simp only [block,fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
    ← jointGate_as_product]

theorem evolve_weight {a : Type} [Fintype a] (U ρ : Mat a) (p : ℂ) :
    evolve U (p • ρ) = p • evolve U ρ := by
  simp [evolve,Matrix.mul_smul,smul_mul_assoc]

/-- Exact history decomposition against every coherent finite-memory tester. -/
theorem run_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) (n : ℕ) :
    run (extension e f δ hδ hδ1) t n =
      (block (((1-δ : ℝ) : ℂ) • run e t n) ((δ : ℂ) • run f t n)).submatrix
        (split e.b f.b (Payload I × Fin r)) (split e.b f.b (Payload I × Fin r)) := by
  induction n with
  | zero => exact initialState_branches e f δ hδ hδ1 t
  | succ n ih =>
    rw [run,run,run]
    split_ifs with h
    · rw [ih,jointGate_branches,evolve_submatrix_equiv (split e.b f.b (Payload I × Fin r)),block_evolve,
        evolve_weight,evolve_weight]
    · exact ih

theorem partialRight_branches {a b : ℕ} {p : Type} [Fintype p]
    (A : Mat (Fin a × p)) (B : Mat (Fin b × p)) :
    partialRight ((block A B).submatrix (split a b p) (split a b p)) =
      (block (partialRight A) (partialRight B)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [partialRight,split,block]

theorem partialLeft_branches {a b : ℕ} {p : Type} [Fintype p]
    (A : Mat (Fin a × p)) (B : Mat (Fin b × p)) :
    partialLeft ((block A B).submatrix (split a b p) (split a b p)) =
      partialLeft A + partialLeft B := by
  ext i j
  change (∑ k, block A B (split a b p (k,i)) (split a b p (k,j))) = _
  have he := Equiv.sum_comp finSumFinEquiv
    (fun k => block A B (split a b p (k,i)) (split a b p (k,j)))
  rw [← he,Fintype.sum_sum_type]
  simp [partialLeft,split,block]

theorem partialRight_weight {a p : Type} [Fintype p] (A : Mat (a × p)) (x : ℂ) :
    partialRight (x • A) = x • partialRight A := by
  ext i j
  simp [partialRight,Finset.mul_sum]

theorem partialLeft_weight {a p : Type} [Fintype a] (A : Mat (a × p)) (x : ℂ) :
    partialLeft (x • A) = x • partialLeft A := by
  ext i j
  simp [partialLeft,Finset.mul_sum]

theorem bodyOutput_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) :
    bodyOutput (extension e f δ hδ hδ1) t =
      (block (((1-δ : ℝ) : ℂ) • bodyOutput e t) ((δ : ℂ) • bodyOutput f t)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold bodyOutput finalState
  rw [run_branches,partialRight_branches,partialRight_weight,partialRight_weight]

theorem observerOutput_branches {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {r : ℕ} (t : Tester S r) :
    observerOutput (extension e f δ hδ hδ1) t =
      ((1-δ : ℝ) : ℂ) • observerOutput e t + (δ : ℂ) • observerOutput f t := by
  unfold observerOutput finalState
  rw [run_branches,partialLeft_branches,partialLeft_weight,partialLeft_weight]

theorem traceNorm_eq_library {a : Type} [Fintype a] [DecidableEq a] (A : Mat a) :
    traceNorm A = Matrix.traceNorm A := by
  rw [Matrix.traceNorm_eq_sum_singularValues]
  simp only [traceNorm,singularValues,conjTranspose_conjTranspose]

theorem density_traceNorm {a : Type} [Fintype a] [DecidableEq a] (ρ : Density a) :
    Matrix.traceNorm ρ.matrix = 1 := by
  have he : ((Matrix.traceNorm ρ.matrix : ℝ) : ℂ) = 1 :=
    ρ.positive.traceNorm_eq_trace.trans ρ.normalized
  simpa using congrArg Complex.re he

theorem density_distance_le_one {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Density a) : traceDistance ρ.matrix σ.matrix ≤ 1 := by
  rw [traceDistance,traceNorm_eq_library]
  have h : Matrix.traceNorm (ρ.matrix - σ.matrix) ≤ 2 := by
    calc Matrix.traceNorm (ρ.matrix - σ.matrix)
        = Matrix.traceNorm (ρ.matrix + -σ.matrix) := by rw [sub_eq_add_neg]
      _ ≤ Matrix.traceNorm ρ.matrix + Matrix.traceNorm (-σ.matrix) := Matrix.traceNorm_add_le _ _
      _ = 2 := by rw [Matrix.traceNorm_neg,density_traceNorm,density_traceNorm]; norm_num
  linarith

theorem mixture_distance {a : Type} [Fintype a] [DecidableEq a]
    (ρ σ : Mat a) (δ : ℝ) (hδ : 0 ≤ δ) :
    traceDistance (((1-δ : ℝ) : ℂ) • ρ + (δ : ℂ) • σ) ρ = δ * traceDistance σ ρ := by
  have he : (((1-δ : ℝ) : ℂ) • ρ + (δ : ℂ) • σ) - ρ = (δ : ℂ) • (σ-ρ) := by
    ext i j
    simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  unfold traceDistance
  rw [he,traceNorm_eq_library,traceNorm_eq_library,Matrix.traceNorm_smul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
  ring

/-- The retained flag changes complete service by at most its rare-branch
probability, uniformly in both tester memory dimension and tester circuit. -/
theorem approximates_left {I : Inventory} {S : Schedule I} (e f : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Approximates (extension e f δ hδ hδ1) e δ := by
  intro r t
  rw [observerOutput_branches,mixture_distance _ _ δ hδ]
  have he := run_density e t (2*S.visits+1)
  have hf := run_density f t (2*S.visits+1)
  let ρ : Density (Payload I × Fin r) :=
    ⟨observerOutput e t,partialLeft_positive he.1,(partialLeft_trace _).trans he.2⟩
  let σ : Density (Payload I × Fin r) :=
    ⟨observerOutput f t,partialLeft_positive hf.1,(partialLeft_trace _).trans hf.2⟩
  exact (mul_le_mul_of_nonneg_left (density_distance_le_one σ ρ) hδ).trans_eq (mul_one δ)

end ClassicalFlag
end ScheduleLaw
