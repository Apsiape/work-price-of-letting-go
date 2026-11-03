import Contract

/-! Density-state invariants derived from the actual finite circuit model. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw

theorem unitary_mul {a : Type} [Fintype a] [DecidableEq a] {U V : Mat a}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  rcases hU with ⟨hU1,hU2⟩
  rcases hV with ⟨hV1,hV2⟩
  constructor
  · simp only [conjTranspose_mul, mul_assoc]
    rw [← mul_assoc Uᴴ U, hU1, one_mul, hV1]
  · simp only [conjTranspose_mul, ← mul_assoc]
    rw [mul_assoc U V Vᴴ, hV2, mul_one, hU2]

theorem unitary_kron {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] {U : Mat a} {V : Mat b}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U ⊗ₖ V) := by
  constructor <;> rw [conjTranspose_kronecker, ← mul_kronecker_mul]
  · rw [hU.1,hV.1,one_kronecker_one]
  · rw [hU.2,hV.2,one_kronecker_one]

theorem unitary_submatrix {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) {U : Mat b}
    (hU : IsUnitary U) : IsUnitary (U.submatrix e e) := by
  constructor <;> rw [conjTranspose_submatrix, submatrix_mul_equiv]
  · rw [hU.1, submatrix_one_equiv]
  · rw [hU.2, submatrix_one_equiv]

theorem jointGate_unitary {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (k : Cut S) :
    IsUnitary (jointGate e t k) := by
  let Ud : Mat (Global e r) :=
    ((e.gate k) ⊗ₖ (1 : Mat (Fin r))).submatrix
      (Equiv.prodAssoc (Fin e.b) (Payload I) (Fin r)).symm
      (Equiv.prodAssoc (Fin e.b) (Payload I) (Fin r)).symm
  let Ut : Mat (Global e r) := (1 : Mat (Fin e.b)) ⊗ₖ
    ((t.gate k).submatrix (Equiv.prodComm (Payload I) (Fin r))
      (Equiv.prodComm (Payload I) (Fin r)))
  have hd : IsUnitary Ud := unitary_submatrix _
    (unitary_kron (e.unitary k) (by constructor <;> simp))
  have ht : IsUnitary Ut := unitary_kron (by constructor <;> simp)
    (unitary_submatrix _ (t.unitary k))
  have he : jointGate e t k = Ut * Ud := by
    rfl
  rw [he]
  exact unitary_mul ht hd

theorem pureMatrix_positive {a : Type} [Fintype a] (v : a → ℂ) :
    (pureMatrix v).PosSemidef := by
  exact posSemidef_vecMulVec_self_star v

theorem pureMatrix_trace {a : Type} [Fintype a] (v : a → ℂ) :
    (pureMatrix v).trace = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp [pureMatrix, trace, Complex.mul_conj, Complex.ofReal_sum]

theorem positive_kron {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] {ρ : Mat a} {σ : Mat b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : (ρ ⊗ₖ σ).PosSemidef := by
  rw [hρ.1.spectral_theorem, hσ.1.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  rw [mul_kronecker_mul, mul_kronecker_mul, ← conjTranspose_kronecker,
    diagonal_kronecker_diagonal]
  apply PosSemidef.mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  rintro ⟨i,j⟩
  change (0 : ℂ) ≤ (hρ.1.eigenvalues i : ℂ) * (hσ.1.eigenvalues j : ℂ)
  rw [← Complex.ofReal_mul]
  exact Complex.nonneg_iff.mpr
    ⟨mul_nonneg (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j), rfl⟩

theorem initialState_density {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    (initialState e t).PosSemidef ∧ (initialState e t).trace = 1 := by
  constructor
  · exact positive_kron e.source.positive (pureMatrix_positive _)
  · rw [initialState, trace_kronecker, e.source.normalized, one_mul, pureMatrix_trace]
    have he : ∑ x : Payload I × Fin r, Complex.normSq (t.initial (x.2,x.1)) = 1 := by
      calc ∑ x : Payload I × Fin r, Complex.normSq (t.initial (x.2,x.1))
          = ∑ j : Fin r, ∑ p : Payload I, Complex.normSq (t.initial (j,p)) := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_comm
        _ = 1 := by simpa only [Fintype.sum_prod_type] using t.normalized
    rw [he, Complex.ofReal_one]

theorem evolve_density {a : Type} [Fintype a] [DecidableEq a]
    (U ρ : Mat a) (hU : IsUnitary U) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (evolve U ρ).PosSemidef ∧ (evolve U ρ).trace = 1 := by
  constructor
  · exact hρ.mul_mul_conjTranspose_same U
  · unfold evolve
    rw [trace_mul_cycle, hU.1, one_mul, htr]

theorem run_density {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) :
    (run e t n).PosSemidef ∧ (run e t n).trace = 1 := by
  induction n with
  | zero => exact initialState_density e t
  | succ n ih =>
    unfold run
    split_ifs with h
    · exact evolve_density _ _ (jointGate_unitary e t ⟨n,h⟩) ih.1 ih.2
    · exact ih

theorem partialRight_positive {a b : Type} [Fintype a] [Fintype b]
    {ρ : Mat (a × b)} (hρ : ρ.PosSemidef) : (partialRight ρ).PosSemidef := by
  have he : partialRight ρ = ∑ j : b, ρ.submatrix (fun i => (i,j)) (fun i => (i,j)) := by
    ext i k
    simp [partialRight, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [he]
  exact posSemidef_sum _ (fun j _ => hρ.submatrix (fun i => (i,j)))

theorem partialLeft_positive {a b : Type} [Fintype a] [Fintype b]
    {ρ : Mat (a × b)} (hρ : ρ.PosSemidef) : (partialLeft ρ).PosSemidef := by
  have he : partialLeft ρ = ∑ j : a, ρ.submatrix (fun i => (j,i)) (fun i => (j,i)) := by
    ext i k
    simp [partialLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [he]
  exact posSemidef_sum _ (fun j _ => hρ.submatrix (fun i => (j,i)))

theorem partialRight_trace {a b : Type} [Fintype a] [Fintype b] (ρ : Mat (a × b)) :
    (partialRight ρ).trace = ρ.trace := by
  simp [partialRight, trace, Fintype.sum_prod_type]

theorem partialLeft_trace {a b : Type} [Fintype a] [Fintype b] (ρ : Mat (a × b)) :
    (partialLeft ρ).trace = ρ.trace := by
  simp only [partialLeft, trace, diag_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem submatrix_trace_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (ρ : Mat b) : (ρ.submatrix e e).trace = ρ.trace := by
  exact Equiv.sum_comp e (fun i => ρ i i)

theorem batteryFinal_density {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :
    (batteryFinal e t).PosSemidef ∧ (batteryFinal e t).trace = 1 := by
  have hf := run_density e.extension t (2*S.visits+1)
  constructor
  · exact partialRight_positive (partialLeft_positive
      ((partialRight_positive hf.1).submatrix e.split.symm))
  · unfold batteryFinal batteryReservoirFinal bodyOutput finalState
    rw [partialRight_trace, partialLeft_trace, submatrix_trace_equiv, partialRight_trace]
    exact hf.2

theorem bodyOutput_density {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    (bodyOutput e t).PosSemidef ∧ (bodyOutput e t).trace = 1 := by
  have hf := run_density e t (2*S.visits+1)
  exact ⟨partialRight_positive hf.1, (partialRight_trace _).trans hf.2⟩

theorem controllerFinal_density {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :
    (controllerFinal e t).PosSemidef ∧ (controllerFinal e t).trace = 1 := by
  have hf := bodyOutput_density e.extension t
  constructor
  · exact partialRight_positive (hf.1.submatrix e.split.symm)
  · unfold controllerFinal
    rw [partialRight_trace,submatrix_trace_equiv]
    exact hf.2

theorem reservoirFinal_density {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) {r : ℕ} (t : Tester S r) :
    (reservoirFinal e t).PosSemidef ∧ (reservoirFinal e t).trace = 1 := by
  have hf := bodyOutput_density e.extension t
  constructor
  · exact partialLeft_positive (partialLeft_positive (hf.1.submatrix e.split.symm))
  · unfold reservoirFinal batteryReservoirFinal
    rw [partialLeft_trace,partialLeft_trace,submatrix_trace_equiv]
    exact hf.2

theorem battery_nonnegative_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) (j : Fin e.w) :
    0 ≤ (batteryFinal e t j j).re := by
  exact (Complex.nonneg_iff.mp (batteryFinal_density e t).1.diag_nonneg).1

theorem battery_normalized_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) :
    ∑ j, (batteryFinal e t j j).re = 1 := by
  have h := congrArg Complex.re (batteryFinal_density e t).2
  simpa [trace] using h

end ScheduleLaw
