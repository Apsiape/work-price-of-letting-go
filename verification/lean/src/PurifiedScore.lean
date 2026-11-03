import CircuitEnergy
import EntropyProducts

/-! The actual inert-purifier circuit, and the paper's S(Z|F) functional. -/
set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw

theorem evolve_kron_one_entry {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (U : Mat a) (ρ : Mat (a × b))
    (i j : a) (k l : b) :
    evolve (U ⊗ₖ (1 : Mat b)) ρ (i,k) (j,l) =
      ∑ y,∑ x,(U i x * ρ (x,k) (y,l)) * star (U j y) := by
  simp only [evolve,mul_apply,Fintype.sum_prod_type,kroneckerMap_apply,
    one_apply,conjTranspose_apply]
  simp [apply_ite,mul_ite,ite_mul,Finset.sum_ite_irrel,Finset.sum_mul]

theorem partialRight_evolve_kron_one {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (U : Mat a) (ρ : Mat (a × b)) :
    partialRight (evolve (U ⊗ₖ (1 : Mat b)) ρ) = evolve U (partialRight ρ) := by
  ext i j
  change (∑ f : b,evolve (U ⊗ₖ (1 : Mat b)) ρ (i,f) (j,f)) =
    evolve U (partialRight ρ) i j
  simp_rw [evolve_kron_one_entry]
  simp only [evolve,mul_apply,partialRight,conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_comm

theorem pureMatrix_mulVec {a b : Type} [Fintype a] [Fintype b]
    (U : Matrix a b ℂ) (v : b → ℂ) :
    pureMatrix (U *ᵥ v) = U * pureMatrix v * Uᴴ := by
  ext i j
  simp only [pureMatrix,mulVec,dotProduct,mul_apply,conjTranspose_apply,
    star_sum,star_mul,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

def historyUnitary {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : ℕ → Mat (Global e r)
  | 0 => 1
  | n+1 => if h : n < 2*S.visits+1 then jointGate e t ⟨n,h⟩ * historyUnitary e t n
    else historyUnitary e t n

theorem historyUnitary_unitary {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) : IsUnitary (historyUnitary e t n) := by
  induction n with
  | zero => constructor <;> simp [historyUnitary]
  | succ n ih =>
    by_cases h : n < 2*S.visits+1
    · simp only [historyUnitary,dif_pos h]
      exact unitary_mul (jointGate_unitary e t ⟨n,h⟩) ih
    · simpa only [historyUnitary,dif_neg h] using ih

theorem run_eq_history {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) :
    run e t n = evolve (historyUnitary e t n) (initialState e t) := by
  induction n with
  | zero => simp [run,historyUnitary,evolve]
  | succ n ih =>
    by_cases h : n < 2*S.visits+1
    · simp only [run,historyUnitary,dif_pos h,ih,evolve_mul]
    · simp only [run,historyUnitary,dif_neg h,ih]

def purifiedInitial {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) : Global e r × Fin e.f → ℂ :=
  fun x => e.purification (x.1.1,x.2) * t.initial (x.1.2.2,x.1.2.1)

def purifiedVector {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) : Global e r × Fin e.f → ℂ :=
  (historyUnitary e t n ⊗ₖ (1 : Mat (Fin e.f))) *ᵥ purifiedInitial e t

theorem purifiedInitial_reduces {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    partialRight (pureMatrix (purifiedInitial e t)) = initialState e t := by
  ext i j
  have hp := congrFun₂ e.purification_reduces i.1 j.1
  change (∑ f,e.purification (i.1,f) * star (e.purification (j.1,f))) = e.source.matrix i.1 j.1 at hp
  simp only [partialRight,pureMatrix,purifiedInitial,initialState,kroneckerMap_apply,star_mul]
  rw [← hp,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem purifiedInitial_reference {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    partialLeft (pureMatrix (purifiedInitial e t)) = partialLeft (pureMatrix e.purification) := by
  have ht := (initialState_density e t).2
  rw [initialState,trace_kronecker,e.source.normalized,one_mul] at ht
  ext f g
  simp only [partialLeft,pureMatrix,purifiedInitial,Fintype.sum_prod_type,star_mul]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (e.purification (b,f) * star (e.purification (b,g))) *
        (pureMatrix (fun x : Payload I × Fin r => t.initial (x.2,x.1))).trace := by
      simp only [trace,diag_apply,pureMatrix,Fintype.sum_prod_type,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    _ = _ := by rw [ht,mul_one]

theorem purifiedVector_reduces {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) :
    partialRight (pureMatrix (purifiedVector e t n)) = run e t n := by
  rw [purifiedVector,pureMatrix_mulVec]
  change partialRight (evolve _ (pureMatrix (purifiedInitial e t))) = _
  rw [partialRight_evolve_kron_one,purifiedInitial_reduces,run_eq_history]

theorem purifiedVector_reference {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) :
    partialLeft (pureMatrix (purifiedVector e t n)) = partialLeft (pureMatrix e.purification) := by
  rw [purifiedVector,pureMatrix_mulVec]
  change partialLeft (evolve _ (pureMatrix (purifiedInitial e t))) = _
  rw [partialLeft_evolve_kron_one _ _ (historyUnitary_unitary e t n),purifiedInitial_reference]

theorem purifiedVector_density {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) (n : ℕ) :
    (pureMatrix (purifiedVector e t n)).PosSemidef ∧
      (pureMatrix (purifiedVector e t n)).trace = 1 := by
  refine ⟨pureMatrix_positive _,?_⟩
  rw [← partialRight_trace, purifiedVector_reduces]
  exact (run_density e t n).2

theorem partialRight_assoc {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (ρ : Mat ((a × b) × c)) :
    partialRight (ρ.submatrix (Equiv.prodAssoc a b c).symm (Equiv.prodAssoc a b c).symm) =
      partialRight (partialRight ρ) := by
  ext i j
  simp [partialRight,Fintype.sum_prod_type]

theorem partialLeft_assoc {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (ρ : Mat ((a × b) × c)) :
    partialLeft (partialLeft (ρ.submatrix (Equiv.prodAssoc a b c).symm
      (Equiv.prodAssoc a b c).symm)) = partialLeft ρ := by
  ext i j
  simp only [partialLeft,submatrix_apply,Equiv.prodAssoc_symm_apply,Fintype.sum_prod_type]
  exact Finset.sum_comm

def purifiedScoreVector {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    Fin e.b × ((Payload I × Fin r) × Fin e.f) → ℂ :=
  fun x => purifiedVector e t (2*S.visits+1) ((x.1,x.2.1),x.2.2)

theorem purifiedScore_density {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    (pureMatrix (purifiedScoreVector e t)).PosSemidef ∧
      (pureMatrix (purifiedScoreVector e t)).trace = 1 := by
  have he : pureMatrix (purifiedScoreVector e t) =
      (pureMatrix (purifiedVector e t (2*S.visits+1))).submatrix
        (Equiv.prodAssoc (Fin e.b) (Payload I × Fin r) (Fin e.f)).symm
        (Equiv.prodAssoc (Fin e.b) (Payload I × Fin r) (Fin e.f)).symm := rfl
  rw [he]
  have h := purifiedVector_density e t (2*S.visits+1)
  exact ⟨h.1.submatrix _,(submatrix_trace_equiv _ _).trans h.2⟩

def purifiedConditionalEntropy {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) : ℝ :=
  entropy (partialLeft (pureMatrix (purifiedScoreVector e t))) -
    entropy (partialLeft (partialLeft (pureMatrix (purifiedScoreVector e t))))

theorem purified_conditional_entropy {I : Inventory} {S : Schedule I}
    (e : Extension S) {r : ℕ} (t : Tester S r) :
    purifiedConditionalEntropy e t = entropy (bodyOutput e t) - entropy e.source.matrix := by
  have he : pureMatrix (purifiedScoreVector e t) =
      (pureMatrix (purifiedVector e t (2*S.visits+1))).submatrix
        (Equiv.prodAssoc (Fin e.b) (Payload I × Fin r) (Fin e.f)).symm
        (Equiv.prodAssoc (Fin e.b) (Payload I × Fin r) (Fin e.f)).symm := rfl
  have hbody : partialRight (pureMatrix (purifiedScoreVector e t)) = bodyOutput e t := by
    rw [he,partialRight_assoc,purifiedVector_reduces]
    rfl
  have hb := pure_complement_entropy (purifiedScoreVector e t)
  rw [hbody] at hb
  have hF := pure_complement_entropy e.purification
  rw [e.purification_reduces] at hF
  unfold purifiedConditionalEntropy
  rw [← hb,he,partialLeft_assoc,purifiedVector_reference,← hF]

theorem score_eq_purified_conditional {I : Inventory} {S : Schedule I}
    (β : ℝ) (e : Extension S) {r : ℕ} (t : Tester S r) :
    score β e t = purifiedConditionalEntropy e t / β + handoff e t := by
  rw [purified_conditional_entropy]
  rfl

theorem held_initial_empty {I : Inventory} (S : Schedule I) :
    held S ⟨0,by omega⟩ = ∅ := by
  ext c
  simp [held]

theorem held_terminal_empty {I : Inventory} (S : Schedule I) :
    held S ⟨2*S.visits,by omega⟩ = ∅ := by
  ext c
  constructor
  · intro hc
    simp only [held,Finset.mem_filter,Finset.mem_univ,true_and] at hc
    obtain ⟨v,_,hv⟩ := hc
    have hr := (S.position (v,true)).isLt
    omega
  · simp

def purifiedFiniteCost {I : Inventory} {S : Schedule I}
    (β : ℝ) (T : Target S) (ε : ℝ) : EReal :=
  ⨅ (e : Extension S) (_ : Approximates e T ε), ⨆ r,⨆ t : Tester S r,
    ((purifiedConditionalEntropy e t / β + handoff e t : ℝ) : EReal)

theorem finiteCost_eq_purified {I : Inventory} {S : Schedule I}
    (β : ℝ) (T : Target S) (ε : ℝ) : finiteCost β T ε = purifiedFiniteCost β T ε := by
  simp only [finiteCost,purifiedFiniteCost,score_eq_purified_conditional]

def purifiedRegularizedCost (β : ℝ) (T : TaskFamily) : EReal :=
  ⨅ (ε : ℕ → ℝ) (_ : (∀ n,0 ≤ ε n) ∧ Vanishes ε),
    limsup (fun n => purifiedFiniteCost β (T.target n) (ε n) / ((n+1 : ℝ) : EReal)) atTop

theorem regularizedCost_eq_purified (β : ℝ) (T : TaskFamily) :
    regularizedCost β T = purifiedRegularizedCost β T := by
  simp only [regularizedCost,purifiedRegularizedCost,finiteCost_eq_purified]

end ScheduleLaw
