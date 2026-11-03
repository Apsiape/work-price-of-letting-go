import GibbsAccounting

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw

theorem entropy_diagonal_real {a : Type} [Fintype a] [DecidableEq a] (p : a → ℝ) :
    entropy (diagonal (fun i => (p i : ℂ))) = ∑ i, Real.negMulLog (p i) := by
  have hh : (diagonal (fun i => (p i : ℂ))).IsHermitian := by
    rw [isHermitian_diagonal_iff]
    intro i
    simp [isSelfAdjoint_iff]
  rw [entropy_eq_charpoly_roots _ hh, charpoly_diagonal, Polynomial.roots_prod]
  · simp [Polynomial.roots_X_sub_C,Multiset.map_map,Function.comp_def]
  · simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero]

theorem entropy_unitary_evolve {a : Type} [Fintype a] [DecidableEq a]
    (U ρ : Mat a) (hU : IsUnitary U) (hρ : ρ.PosSemidef) :
    entropy (evolve U ρ) = entropy ρ := by
  change entropy (U * ρ * Uᴴ) = entropy ρ
  rw [entropy_eq_charpoly_roots _ (hρ.mul_mul_conjTranspose_same U).isHermitian,
    entropy_eq_charpoly_roots _ hρ.isHermitian]
  rw [charpoly_mul_comm, ← mul_assoc, hU.1, one_mul]

theorem negMulLog_mul_nonnegative {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x*y) = y * Real.negMulLog x + x * Real.negMulLog y := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  simp only [Real.negMulLog,Real.log_mul hx0 hy0]
  ring

theorem entropy_density_product {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ρ : Density a) (σ : Density b) :
    entropy (ρ.matrix ⊗ₖ σ.matrix) = entropy ρ.matrix + entropy σ.matrix := by
  let U : Mat (a × b) := ρ.positive.isHermitian.eigenvectorUnitary ⊗ₖ
    σ.positive.isHermitian.eigenvectorUnitary
  let p := ρ.positive.isHermitian.eigenvalues
  let q := σ.positive.isHermitian.eigenvalues
  let D : Mat (a × b) := diagonal (fun i => ((p i.1 * q i.2 : ℝ) : ℂ))
  have hp : ∀ i, 0 ≤ p i := ρ.positive.eigenvalues_nonneg
  have hq : ∀ i, 0 ≤ q i := σ.positive.eigenvalues_nonneg
  have hD : D.PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i
    exact Complex.nonneg_iff.mpr ⟨mul_nonneg (hp i.1) (hq i.2),rfl⟩
  have hU : IsUnitary U := unitary_kron
    ⟨ρ.positive.isHermitian.eigenvectorUnitary.2.1,ρ.positive.isHermitian.eigenvectorUnitary.2.2⟩
    ⟨σ.positive.isHermitian.eigenvectorUnitary.2.1,σ.positive.isHermitian.eigenvectorUnitary.2.2⟩
  have he : ρ.matrix ⊗ₖ σ.matrix = evolve U D := by
    rw [ρ.positive.isHermitian.spectral_theorem,σ.positive.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply,star_eq_conjTranspose,
      mul_kronecker_mul,← conjTranspose_kronecker,diagonal_kronecker_diagonal]
    simp only [evolve,U,D,p,q,Complex.ofReal_mul]
    rfl
  rw [he,entropy_unitary_evolve U D hU hD,entropy_diagonal_real]
  rw [entropy_of_hermitian _ ρ.positive.isHermitian,
    entropy_of_hermitian _ σ.positive.isHermitian]
  change (∑ i : a × b, Real.negMulLog (p i.1 * q i.2)) =
    (∑ i, Real.negMulLog (p i)) + ∑ j, Real.negMulLog (q j)
  rw [Fintype.sum_prod_type]
  simp_rw [negMulLog_mul_nonnegative (hp _) (hq _),Finset.sum_add_distrib]
  simp only [← Finset.sum_mul,← Finset.mul_sum]
  have hsρ : ∑ i, p i = 1 := density_eigenvalues_sum ρ
  have hsσ : ∑ i, q i = 1 := density_eigenvalues_sum σ
  rw [hsρ,hsσ]
  ring

theorem entropy_reindex {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (ρ : Mat b) (hρ : ρ.IsHermitian) :
    entropy (ρ.submatrix e e) = entropy ρ := by
  rw [entropy_eq_charpoly_roots _ (hρ.submatrix e),entropy_eq_charpoly_roots _ hρ]
  change (((ρ.reindex e.symm e.symm).charpoly.roots).map _).sum = _
  rw [charpoly_reindex]

theorem sharp_entropy {a : Type} [Fintype a] [DecidableEq a] (j : a) :
    entropy (pureMatrix (fun i : a => if i = j then 1 else 0)) = 0 := by
  have he : pureMatrix (fun i : a => if i = j then 1 else 0) =
      diagonal (fun i => ((if i = j then 1 else 0 : ℝ) : ℂ)) := by
    ext i k
    by_cases hi : i = j <;> by_cases hk : k = j <;>
      simp_all [pureMatrix,diagonal_apply,eq_comm]
  rw [he,entropy_diagonal_real]
  simp [Real.negMulLog,apply_ite]

theorem source_entropy_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) : entropy e.extension.source.matrix =
      entropy e.controller.matrix + entropy (gibbs β e.HR) := by
  letI : Nonempty (Fin e.r) := ⟨⟨0,e.r_pos⟩⟩
  let σ : Density (Fin e.w) :=
    ⟨pureMatrix (fun i => if i = e.initialLevel then 1 else 0),
      pureMatrix_positive _,by rw [pureMatrix_trace]; simp⟩
  let γ : Density (Fin e.r) := ⟨gibbs β e.HR,gibbs_positive β e.HR,gibbs_trace β e.HR⟩
  let σγ : Density (Fin e.w × Fin e.r) :=
    ⟨σ.matrix ⊗ₖ γ.matrix,positive_kron σ.positive γ.positive,
      by rw [trace_kronecker,σ.normalized,γ.normalized,one_mul]⟩
  rw [e.source_product,entropy_reindex e.split _
    (positive_kron e.controller.positive σγ.positive).isHermitian]
  change entropy (e.controller.matrix ⊗ₖ σγ.matrix) = _
  rw [entropy_density_product e.controller σγ]
  change entropy e.controller.matrix + entropy (σ.matrix ⊗ₖ γ.matrix) = _
  rw [entropy_density_product σ γ]
  have hs : entropy σ.matrix = 0 := sharp_entropy e.initialLevel
  rw [hs,zero_add]

theorem entropy_accounting_from_circuit {I : Inventory} {S : Schedule I} {β : ℝ}
    (e : Engine S β) (r : ℕ) (t : Tester S r) :
    (engineLedger e t).deviceEntropy = (engineLedger e t).controllerEntropy +
      (engineLedger e t).batteryEntropy + (engineLedger e t).reservoirEntropy -
        (engineLedger e t).totalCorrelation := by
  have hs := source_entropy_from_circuit e
  dsimp [engineLedger,controllerEntropyChange]
  rw [hs]
  ring

end ScheduleLaw
