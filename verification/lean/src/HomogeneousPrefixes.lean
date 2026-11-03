import RetainedEffect

/-! Homogeneous causal equations, their forced normalization, and positivity
of every earlier prefix from positivity of the terminal prefix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

def HomogeneousPrefixEquations {I : Inventory} (S : Schedule I) (a : ℝ)
    (Z : PrefixMatrices S) : Prop :=
  (∀ b, (inputRank b).val = 0 → partialLeft (Z b) = (a : ℂ) • 1) ∧
    (∀ b (hb : 0 < (inputRank b).val), tracePrefixInputs b hb (Z b) =
      (1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ Z (previousInput b hb))

theorem homogeneous_of_causal {I : Inventory} (S : Schedule I) (Z : PrefixMatrices S)
    (hZ : IsCausalPrefixFamily S Z) : HomogeneousPrefixEquations S 1 Z := by
  simpa only [HomogeneousPrefixEquations,Complex.ofReal_one,one_smul] using hZ.2

theorem homogeneous_zero {I : Inventory} (S : Schedule I) :
    HomogeneousPrefixEquations S 0 0 := by
  constructor
  · intro b hb; ext i j; simp [partialLeft]
  · intro b hb
    unfold tracePrefixInputs withNewOutputsFirst traceNewInputs
    ext i j
    simp [partialRight]

theorem homogeneous_add {I : Inventory} (S : Schedule I) (a b : ℝ)
    (Z W : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z)
    (hW : HomogeneousPrefixEquations S b W) :
    HomogeneousPrefixEquations S (a+b) (Z+W) := by
  constructor
  · intro k hk
    change partialLeft (Z k + W k) = _
    rw [partialLeft_additive,hZ.1 k hk,hW.1 k hk,← add_smul,Complex.ofReal_add]
  · intro k hk
    change tracePrefixInputs k hk (Z k + W k) = _
    rw [tracePrefixInputs_add,hZ.2 k hk,hW.2 k hk]
    exact (kronecker_add _ _ _).symm

theorem homogeneous_smul {I : Inventory} (S : Schedule I) (a b : ℝ)
    (Z : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z) :
    HomogeneousPrefixEquations S (b*a) (b • Z) := by
  constructor
  · intro k hk
    change partialLeft ((b : ℂ) • Z k) = _
    rw [ClassicalFlag.partialLeft_weight,hZ.1 k hk,smul_smul,Complex.ofReal_mul]
  · intro k hk
    change tracePrefixInputs k hk ((b : ℂ) • Z k) = _
    rw [tracePrefixInputs_weight,hZ.2 k hk]
    ext i j
    simp only [Pi.smul_apply,Matrix.smul_apply,kroneckerMap_apply,smul_eq_mul,
      Complex.real_smul]
    ring

theorem homogeneous_prefix_trace {I : Inventory} (S : Schedule I) (a : ℝ)
    (Z : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z) (b : InputBurst S) :
    (Z b).trace = (a : ℂ) * prefixDimension b := by
  have aux : ∀ k : ℕ, ∀ b : InputBurst S, (inputRank b).val = k →
      (Z b).trace = (a : ℂ) * prefixDimension b := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro b hb
      by_cases hz : k = 0
      · have he := hZ.1 b (hb.trans hz)
        calc (Z b).trace = (partialLeft (Z b)).trace := (partialLeft_trace _).symm
          _ = (a : ℂ) * prefixDimension b := by
            rw [he,trace_smul,trace_one,registers_card]
            rfl
      · have hp : 0 < (inputRank b).val := by omega
        have hr := previous_rank b hp
        have ht := ih (inputRank (previousInput b hp)).val (by omega) (previousInput b hp) rfl
        have he := congrArg Matrix.trace (hZ.2 b hp)
        rw [tracePrefixInputs_trace,trace_kronecker,trace_one,registers_card,ht] at he
        rw [he,prefix_dimension_step b hp,Nat.cast_mul]
        ring
  exact aux _ b rfl

theorem tracePrefixInputs_positive {I : Inventory} {S : Schedule I} (b : InputBurst S)
    (hb : 0 < (inputRank b).val) (Z : Mat (PrefixSpace b)) (hZ : Z.PosSemidef) :
    (tracePrefixInputs b hb Z).PosSemidef := by
  unfold tracePrefixInputs withNewOutputsFirst traceNewInputs
  exact (partialRight_positive (hZ.submatrix _)).submatrix _

theorem previous_prefix_positive {I : Inventory} {S : Schedule I} (a : ℝ)
    (Z : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z)
    (b : InputBurst S) (hb : 0 < (inputRank b).val) (hpos : (Z b).PosSemidef) :
    (Z (previousInput b hb)).PosSemidef := by
  have ht := tracePrefixInputs_positive b hb (Z b) hpos
  rw [hZ.2 b hb] at ht
  let z : Registers S (newOutputs b hb) := Classical.choice inferInstance
  have hs := ht.submatrix (fun i => (z,i))
  have he : ((1 : Mat (Registers S (newOutputs b hb))) ⊗ₖ Z (previousInput b hb)).submatrix
      (fun i => (z,i)) (fun i => (z,i)) = Z (previousInput b hb) := by ext i j; simp
  rw [he] at hs
  exact hs

theorem input_burst_is_visit {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    ∃ v, inputBurst v = b := by
  have hp := S.position.apply_symm_apply b.val.val
  generalize he : S.position.symm b.val.val = x at hp
  rcases x with ⟨w,q⟩
  have hq : q = false := by
    have hk := b.property
    simpa only [kind,dif_pos b.val.val.isLt,he] using hk
  subst q
  refine ⟨w,?_⟩
  apply Subtype.ext
  change burstOf (S.position (w,false)) = b.val
  rw [hp]
  exact (burstOf_unique b.val.val b.val).mp (first_mem b.val)

theorem input_le_last {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (b : InputBurst S) : b ≤ lastInputBurst S h := by
  obtain ⟨v,rfl⟩ := input_burst_is_visit b
  exact inputBurst_le_of_arrival_le v _ (all_inputs_before_last S h v)

theorem homogeneous_prefixes_positive {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (a : ℝ) (Z : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z)
    (hpos : (Z (lastInputBurst S h)).PosSemidef) : ∀ b, (Z b).PosSemidef := by
  let N := (inputRank (lastInputBurst S h)).val
  have aux : ∀ n : ℕ, ∀ b : InputBurst S, N - (inputRank b).val = n → (Z b).PosSemidef := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hb
      by_cases he : b = lastInputBurst S h
      · subst b; exact hpos
      · have hlt : b < lastInputBurst S h := lt_of_le_of_ne (input_le_last S h b) he
        have hr := (inputEnumeration S).symm.strictMono hlt
        change (inputRank b).val < N at hr
        let next : InputBurst S := inputEnumeration S
          ⟨(inputRank b).val+1,by have := (inputRank (lastInputBurst S h)).isLt; omega⟩
        have hn : (inputRank next).val = (inputRank b).val+1 := by
          simp only [next,inputRank,OrderIso.symm_apply_apply]
        have hp : 0 < (inputRank next).val := by omega
        have heq : previousInput next hp = b := by
          apply (inputEnumeration S).symm.injective
          apply Fin.ext
          change (inputRank (previousInput next hp)).val = (inputRank b).val
          have := previous_rank next hp
          omega
        have hnext := ih (N - (inputRank next).val) (by omega) next rfl
        have hprev := previous_prefix_positive a Z hZ next hp hnext
        rw [heq] at hprev
        exact hprev
  exact fun b => aux _ b rfl

theorem homogeneous_normalize {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (a : ℝ) (ha : 0 < a) (Z : PrefixMatrices S) (hZ : HomogeneousPrefixEquations S a Z)
    (hpos : (Z (lastInputBurst S h)).PosSemidef) : IsCausalPrefixFamily S (a⁻¹ • Z) := by
  have hn := homogeneous_smul S a a⁻¹ Z hZ
  rw [inv_mul_cancel₀ (ne_of_gt ha)] at hn
  refine ⟨fun b => (homogeneous_prefixes_positive S h a Z hZ hpos b).smul
    (show (0 : ℂ) ≤ (a⁻¹ : ℝ) by exact_mod_cast inv_nonneg.mpr ha.le),?_,hn.2⟩
  simpa only [Complex.ofReal_one,one_smul] using hn.1

end ScheduleLaw.History
