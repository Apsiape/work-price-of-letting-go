import BurstHistory
import TesterWiring
import ClassicalFlag

/-! Accessible record marginals and independently routed open-output Grams. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

abbrev Registers {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :=
  (v : {v // v ∈ V}) → Fin (I.dim (S.carrier v.val))

def registerPartition {I : Inventory} (S : Schedule I) (V : Finset (Fin S.visits)) :
    Recorder.Inputs S ≃ Registers S V × Registers S Vᶜ where
  toFun a := (fun v => a v.val,fun v => a v.val)
  invFun a v := if h : v ∈ V then a.1 ⟨v,h⟩ else a.2 ⟨v,Finset.mem_compl.mpr h⟩
  left_inv a := by funext v; by_cases h : v ∈ V <;> simp [h]
  right_inv a := by
    apply Prod.ext
    · funext v; simp [v.property]
    · funext v; simp [Finset.mem_compl.mp v.property]

abbrev Record {I : Inventory} (S : Schedule I) (A O : Finset (Fin S.visits)) :=
  Registers S A × Registers S O

def stockPartition {I : Inventory} (S : Schedule I) (A O : Finset (Fin S.visits)) :
    Recorder.Stock S ≃ Record S A O × Record S Aᶜ Oᶜ :=
  (Equiv.prodCongr (registerPartition S A) (registerPartition S O)).trans
    (Equiv.prodProdProdComm _ _ _ _)

def recordCoordinates {I : Inventory} (S : Schedule I) (r : ℕ)
    (A O : Finset (Fin S.visits)) :
    Raw S r ≃ Record S A O × (Record S Aᶜ Oᶜ × (Payload I × Fin r)) :=
  (Equiv.prodCongr (stockPartition S A O) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

def physicalCoordinates {I : Inventory} (S : Schedule I) (r : ℕ)
    (A O : Finset (Fin S.visits)) :
    Record S A O × (Record S Aᶜ Oᶜ × (Payload I × Fin r)) ≃ Global (Recorder.extension S) r :=
  (recordCoordinates S r A O).symm.trans (actual S r)

/-- This is the actual reduced state of selected retained visit registers. -/
def chi {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (n : ℕ)
    (A O : Finset (Fin S.visits)) : Mat (Record S A O) :=
  partialRight ((run (Recorder.extension S) t n).submatrix
    (physicalCoordinates S r A O) (physicalCoordinates S r A O))

def outputDimension {I : Inventory} (S : Schedule I) (O : Finset (Fin S.visits)) : ℕ :=
  ∏ v ∈ O, I.dim (S.carrier v)

def outputNorm {I : Inventory} (S : Schedule I) (O : Finset (Fin S.visits)) : ℝ :=
  ∏ v ∈ O, Real.sqrt (I.dim (S.carrier v))

/-- Released-output EPR wires are unnormalized Choi wires. Every other stock
pair remains normalized. This source is specified entrywise, without run. -/
def openSource {I : Inventory} (S : Schedule I) (O : Finset (Fin S.visits))
    (x : Recorder.Stock S) : ℂ :=
  ∏ v, if v ∈ O then (if x.1 v = x.2 v then 1 else 0)
    else Recorder.epr (x.1 v,x.2 v)

/-- The Gram is obtained from the tester-only amplitude recurrence, with past
output ports open and the other normalized pair factors traced. -/
def gram {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (n : ℕ)
    (A O : Finset (Fin S.visits)) : Mat (Record S A O) :=
  partialRight (pureMatrix (fun x =>
    amplitudes t (openSource S O) n ((recordCoordinates S r A O).symm x)))

theorem outputDimension_pos {I : Inventory} (S : Schedule I) (O : Finset (Fin S.visits)) :
    0 < outputDimension S O := Finset.prod_pos (fun v _ => I.dim_pos (S.carrier v))

theorem outputNorm_sq {I : Inventory} (S : Schedule I) (O : Finset (Fin S.visits)) :
    outputNorm S O ^ 2 = outputDimension S O := by
  simp only [outputNorm,outputDimension,← Finset.prod_pow,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro v _
  exact Real.sq_sqrt (Nat.cast_nonneg _)

theorem openSource_scale {I : Inventory} (S : Schedule I) (O : Finset (Fin S.visits)) :
    openSource S O = (outputNorm S O : ℂ) • (Recorder.epr (a := Recorder.Inputs S)) := by
  funext x
  have hpair (v : Fin S.visits) :
      (if x.1 v = x.2 v then (1 : ℂ) else 0) =
        (Real.sqrt (I.dim (S.carrier v)) : ℂ) * Recorder.epr (x.1 v,x.2 v) := by
    have hs : (Real.sqrt (I.dim (S.carrier v)) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (I.dim_pos (S.carrier v))))
    by_cases h : x.1 v = x.2 v
    · simp only [Recorder.epr,h,if_true,Fintype.card_fin,Complex.ofReal_inv]
      exact (mul_inv_cancel₀ hs).symm
    · simp [Recorder.epr,h]
  calc openSource S O x
      = ∏ v, (if v ∈ O then (Real.sqrt (I.dim (S.carrier v)) : ℂ) else 1) *
          Recorder.epr (x.1 v,x.2 v) := by
        apply Finset.prod_congr rfl
        intro v _
        by_cases h : v ∈ O
        · simpa only [if_pos h] using hpair v
        · simp only [if_neg h,one_mul]
    _ = (∏ v, if v ∈ O then (Real.sqrt (I.dim (S.carrier v)) : ℂ) else 1) *
        (∏ v, Recorder.epr (x.1 v,x.2 v)) := Finset.prod_mul_distrib
    _ = (outputNorm S O : ℂ) * Recorder.epr x := by
      rw [← Recorder.epr_visit_product]
      congr 1
      simp only [← Finset.prod_filter]
      simp [outputNorm,Complex.ofReal_prod]

theorem chi_density {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) (n : ℕ)
    (A O : Finset (Fin S.visits)) :
    (chi t n A O).PosSemidef ∧ (chi t n A O).trace = 1 := by
  have hd := run_density (Recorder.extension S) t n
  exact ⟨partialRight_positive (hd.1.submatrix _),by
    rw [chi,partialRight_trace,submatrix_trace_equiv]
    exact hd.2⟩

theorem normalized_gram_physical {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (n : ℕ) (A O : Finset (Fin S.visits)) :
    partialRight (pureMatrix (fun x =>
      amplitudes t Recorder.epr n ((recordCoordinates S r A O).symm x))) = chi t n A O := by
  have he : ((run (Recorder.extension S) t n).submatrix (physicalCoordinates S r A O)
      (physicalCoordinates S r A O)) =
      ((run (Recorder.extension S) t n).submatrix (actual S r) (actual S r)).submatrix
        (recordCoordinates S r A O).symm (recordCoordinates S r A O).symm := rfl
  rw [chi,he,run_amplitudes]
  rfl

theorem gram_physical {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (n : ℕ) (A O : Finset (Fin S.visits)) :
    gram t n A O = (outputDimension S O : ℂ) • chi t n A O := by
  have he : (fun x => amplitudes t (openSource S O) n ((recordCoordinates S r A O).symm x)) =
      (outputNorm S O : ℂ) •
        (fun x => amplitudes t Recorder.epr n ((recordCoordinates S r A O).symm x)) := by
    rw [openSource_scale,amplitudes_scale]
    rfl
  rw [gram,he,pureMatrix_scale,ClassicalFlag.partialRight_weight,normalized_gram_physical]
  have hn : Complex.normSq (outputNorm S O : ℂ) = (outputDimension S O : ℝ) := by
    rw [Complex.normSq_ofReal,← pow_two,outputNorm_sq]
  rw [hn]
  simp

/-- Exact recorder identity with the product of open-output dimensions. The
right-hand Gram is defined by independent routed tester amplitudes. -/
theorem recorder_identity {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (n : ℕ) (A O : Finset (Fin S.visits)) :
    chi t n A O = (outputDimension S O : ℂ)⁻¹ • gram t n A O := by
  have hc : (outputDimension S O : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (outputDimension_pos S O)
  rw [gram_physical,smul_smul,inv_mul_cancel₀ hc,one_smul]

def prefixChi {I : Inventory} {S : Schedule I} {r : ℕ} (b : InputBurst S) (t : Tester S r) :
    Mat (InputPrefix b × OutputPrefix b) :=
  chi t (recordTime b) (arrived S (recordTime b)) (released S (recordTime b))

def prefixGram {I : Inventory} {S : Schedule I} {r : ℕ} (b : InputBurst S) (t : Tester S r) :
    Mat (InputPrefix b × OutputPrefix b) :=
  gram t (recordTime b) (arrived S (recordTime b)) (released S (recordTime b))

def prefixDimension {I : Inventory} {S : Schedule I} (b : InputBurst S) : ℕ :=
  outputDimension S (released S (recordTime b))

theorem prefix_recorder_identity {I : Inventory} {S : Schedule I} {r : ℕ}
    (b : InputBurst S) (t : Tester S r) :
    prefixChi b t = (prefixDimension b : ℂ)⁻¹ • prefixGram b t :=
  recorder_identity t (recordTime b) _ _

theorem gram_positive {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (n : ℕ) (A O : Finset (Fin S.visits)) : (gram t n A O).PosSemidef :=
  partialRight_positive (pureMatrix_positive _)

theorem gram_trace {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (n : ℕ) (A O : Finset (Fin S.visits)) :
    (gram t n A O).trace = outputDimension S O := by
  rw [gram_physical,trace_smul,(chi_density t n A O).2,smul_eq_mul,mul_one]

theorem density_subsingleton {a : Type} [Fintype a] [DecidableEq a] [Subsingleton a]
    [Nonempty a] (ρ : Density a) : ρ.matrix = 1 := by
  ext i j
  letI : Unique a := ⟨⟨i⟩,fun j => Subsingleton.elim j i⟩
  have he : ρ.matrix i i = 1 := by simpa only [trace,diag_apply,Fintype.sum_unique] using ρ.normalized
  have hij := Subsingleton.elim i j
  subst j
  simpa using he

theorem zero_visits_record {I : Inventory} (S : Schedule I) (hz : S.visits = 0)
    {r : ℕ} (t : Tester S r) (n : ℕ) (A O : Finset (Fin S.visits)) :
    chi t n A O = 1 ∧ gram t n A O = 1 ∧ outputDimension S O = 1 := by
  haveI : IsEmpty (Fin S.visits) := by rw [hz]; infer_instance
  haveI : Nonempty (Registers S A) := ⟨fun v => ⟨0,I.dim_pos (S.carrier v.val)⟩⟩
  haveI : Nonempty (Registers S O) := ⟨fun v => ⟨0,I.dim_pos (S.carrier v.val)⟩⟩
  have hc : outputDimension S O = 1 := by simp [outputDimension]
  have hd := chi_density t n A O
  have he := density_subsingleton (⟨chi t n A O,hd.1,hd.2⟩ : Density (Record S A O))
  change chi t n A O = 1 at he
  exact ⟨he,by rw [gram_physical,hc,Nat.cast_one,one_smul,he],hc⟩

end History
end ScheduleLaw
