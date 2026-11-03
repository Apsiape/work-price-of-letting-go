import ScheduleEnergy
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
Visit-indexed recorder hardware. Every actual visit has a separate input register
and EPR partner. The physical payload retains its original carrier identities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace Recorder

/-- One register of the dimension of the physical carrier, for every visit. -/
abbrev Inputs {I : Inventory} (S : Schedule I) :=
  (v : Fin S.visits) → Fin (I.dim (S.carrier v))

/-- Both halves of all pairs are counted in the retained body. -/
abbrev Stock {I : Inventory} (S : Schedule I) := Inputs S × Inputs S

instance inputsNonempty {I : Inventory} (S : Schedule I) : Nonempty (Inputs S) :=
  ⟨fun v => ⟨0, I.dim_pos (S.carrier v)⟩⟩

theorem inputs_card_pos {I : Inventory} (S : Schedule I) :
    0 < Fintype.card (Inputs S) := Fintype.card_pos

def epr {a : Type} [Fintype a] [DecidableEq a] (x : a × a) : ℂ :=
  if x.1 = x.2 then ((Real.sqrt (Fintype.card a))⁻¹ : ℝ) else 0

theorem epr_normSq {a : Type} [Fintype a] [DecidableEq a] (x : a × a) :
    Complex.normSq (epr x) =
      if x.1 = x.2 then (Fintype.card a : ℝ)⁻¹ else 0 := by
  by_cases h : x.1 = x.2
  · simp only [epr, if_pos h, Complex.normSq_ofReal, inv_pow]
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  · simp [epr,h]

theorem epr_normalized {a : Type} [Fintype a] [DecidableEq a] [Nonempty a] :
    ∑ x : a × a, Complex.normSq (epr x) = 1 := by
  simp_rw [epr_normSq]
  rw [Fintype.sum_prod_type]
  simp [Fintype.card_ne_zero]

theorem epr_reduction {a : Type} [Fintype a] [DecidableEq a] :
    partialRight (pureMatrix (epr (a := a))) =
      diagonal (fun _ => ((Fintype.card a : ℝ)⁻¹ : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    change (∑ k, epr (i,k) * starRingEnd ℂ (epr (i,k))) = _
    simp_rw [Complex.mul_conj]
    simp [epr_normSq, ← Complex.ofReal_sum]
  · simp [partialRight,pureMatrix,epr,diagonal_apply,h,Ne.symm h]

/-- The global diagonal vector is exactly the product of independently
normalized EPR pairs, one for each visit (also when there are no visits). -/
theorem epr_visit_product {I : Inventory} (S : Schedule I) (a r : Inputs S) :
    epr (a,r) = ∏ v, epr (a v,r v) := by
  have hc : (Fintype.card (Inputs S) : ℝ) =
      ∏ v, (Fintype.card (Fin (I.dim (S.carrier v))) : ℝ) := by
    simp only [Inputs,Fintype.card_pi,Nat.cast_prod]
  have hs : Real.sqrt (Fintype.card (Inputs S)) =
      ∏ v, Real.sqrt (Fintype.card (Fin (I.dim (S.carrier v)))) := by
    rw [hc,Real.sqrt_prod]
    intro v _
    exact Nat.cast_nonneg _
  simp only [epr,Fintype.prod_ite_zero,← funext_iff]
  by_cases h : a = r
  · simp only [h,if_true]
    rw [hs]
    simp only [Complex.ofReal_inv,Complex.ofReal_prod,Finset.prod_inv_distrib]
  · simp only [h,if_false]

/-- Swapping the incoming physical carrier with the fresh register for this
visit. The second register bank is retained and never touched by a contact. -/
def swapAt {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (x : Stock S × Payload I) : Stock S × Payload I :=
  ((Function.update x.1.1 v (x.2 (S.carrier v)),x.1.2),
    Function.update x.2 (S.carrier v) (x.1.1 v))

theorem swapAt_involutive {I : Inventory} {S : Schedule I} (v : Fin S.visits) :
    Function.Involutive (swapAt v) := by
  rintro ⟨⟨a,r⟩,p⟩
  apply Prod.ext
  · apply Prod.ext
    · funext w
      by_cases h : w = v
      · subst w; simp [swapAt]
      · simp [swapAt,Function.update_of_ne h]
    · rfl
  · funext c
    by_cases h : c = S.carrier v
    · subst c; simp [swapAt]
    · simp [swapAt,Function.update_of_ne h]

def swapEquiv {I : Inventory} {S : Schedule I} (v : Fin S.visits) :
    Equiv.Perm (Stock S × Payload I) :=
  (swapAt_involutive v).toPerm

theorem swapAt_input {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (x : Stock S × Payload I) : (swapAt v x).1.1 v = x.2 (S.carrier v) := by
  simp [swapAt]

theorem swapAt_payload {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (x : Stock S × Payload I) : (swapAt v x).2 (S.carrier v) = x.1.1 v := by
  simp [swapAt]

theorem swapAt_other_input {I : Inventory} {S : Schedule I}
    (v w : Fin S.visits) (h : w ≠ v) (x : Stock S × Payload I) :
    (swapAt v x).1.1 w = x.1.1 w := by
  simp [swapAt,Function.update_of_ne h]

theorem swapAt_other_carrier {I : Inventory} {S : Schedule I}
    (v : Fin S.visits) (c : Fin I.count) (h : c ≠ S.carrier v)
    (x : Stock S × Payload I) : (swapAt v x).2 c = x.2 c := by
  simp [swapAt,Function.update_of_ne h]

theorem swapAt_partner {I : Inventory} {S : Schedule I}
    (v : Fin S.visits) (x : Stock S × Payload I) : (swapAt v x).1.2 = x.1.2 := rfl

theorem permutation_unitary {a : Type} [Fintype a] [DecidableEq a]
    (σ : Equiv.Perm a) : IsUnitary (σ.permMatrix ℂ) := by
  constructor <;> simp [conjTranspose_permMatrix, ← permMatrix_mul]

/-- This identity holds for arbitrary matrices, including off-diagonal history
terms. It therefore retains incoming correlations with any untouched system. -/
theorem permutation_evolve {a : Type} [Fintype a] [DecidableEq a]
    (σ : Equiv.Perm a) (ρ : Mat a) :
    evolve (σ.permMatrix ℂ) ρ = ρ.submatrix σ σ := by
  ext i j
  simp [evolve,Matrix.mul_apply,Equiv.Perm.permMatrix,PEquiv.toMatrix,
    Equiv.toPEquiv_apply]

theorem permutation_entry {a : Type} [DecidableEq a] (σ : Equiv.Perm a) (i j : a) :
    σ.permMatrix ℂ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix,PEquiv.toMatrix,eq_comm]

/-- A permutation that splits into a local permutation and the identity is a
square local unitary in the original, matrix-entry definition of locality. -/
theorem local_permutation (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (σ : Equiv.Perm (Fin b × Payload I))
    (τ : Equiv.Perm (Fin b × Restricted I A))
    (hσ : ∀ x, bodyPartition I b A (σ x) =
      (τ (bodyPartition I b A x).1,(bodyPartition I b A x).2)) :
    LocalOn I b A (σ.permMatrix ℂ) := by
  refine ⟨τ.permMatrix ℂ,permutation_unitary τ,?_⟩
  intro i j
  have he : σ i = j ↔
      τ (bodyPartition I b A i).1 = (bodyPartition I b A j).1 ∧
      (bodyPartition I b A i).2 = (bodyPartition I b A j).2 := by
    rw [← (bodyPartition I b A).injective.eq_iff,hσ,Prod.mk.injEq]
  simp only [permutation_entry]
  change (if σ i = j then (1 : ℂ) else 0) =
    (if τ (bodyPartition I b A i).1 = (bodyPartition I b A j).1 then 1 else 0) *
      if (bodyPartition I b A i).2 = (bodyPartition I b A j).2 then 1 else 0
  split_ifs <;> simp_all

def stockFin {I : Inventory} (S : Schedule I) : Stock S ≃ Fin (Fintype.card (Stock S)) :=
  Fintype.equivFin _

def swapFin {I : Inventory} {S : Schedule I} (v : Fin S.visits) :
    Equiv.Perm (Fin (Fintype.card (Stock S)) × Payload I) :=
  (Equiv.prodCongr (stockFin S).symm (Equiv.refl _)).trans
    ((swapEquiv v).trans (Equiv.prodCongr (stockFin S) (Equiv.refl _)))

def swapHeldAt {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (A : Finset (Fin I.count)) (hc : S.carrier v ∈ A)
    (x : Stock S × Restricted I A) : Stock S × Restricted I A :=
  ((Function.update x.1.1 v (x.2 ⟨S.carrier v,hc⟩),x.1.2),
    Function.update x.2 ⟨S.carrier v,hc⟩ (x.1.1 v))

theorem swapHeldAt_involutive {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (A : Finset (Fin I.count)) (hc : S.carrier v ∈ A) :
    Function.Involutive (swapHeldAt v A hc) := by
  rintro ⟨⟨a,r⟩,p⟩
  apply Prod.ext
  · apply Prod.ext
    · funext w
      by_cases h : w = v
      · subst w; simp [swapHeldAt]
      · simp [swapHeldAt,Function.update_of_ne h]
    · rfl
  · funext c
    by_cases h : c = ⟨S.carrier v,hc⟩
    · subst c; simp [swapHeldAt]
    · simp [swapHeldAt,Function.update_of_ne h]

def swapHeldFin {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (A : Finset (Fin I.count)) (hc : S.carrier v ∈ A) :
    Equiv.Perm (Fin (Fintype.card (Stock S)) × Restricted I A) :=
  (Equiv.prodCongr (stockFin S).symm (Equiv.refl _)).trans
    (((swapHeldAt_involutive v A hc).toPerm).trans
      (Equiv.prodCongr (stockFin S) (Equiv.refl _)))

theorem swapFin_local {I : Inventory} {S : Schedule I} (v : Fin S.visits)
    (A : Finset (Fin I.count)) (hc : S.carrier v ∈ A) :
    LocalOn I (Fintype.card (Stock S)) A ((swapFin v).permMatrix ℂ) := by
  apply local_permutation I _ A (swapFin v) (swapHeldFin v A hc)
  intro x
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext c
      by_cases h : c.val = S.carrier v
      · have he : c = ⟨S.carrier v,hc⟩ := Subtype.ext h
        subst c
        simp [bodyPartition,payloadPartition,restrictPayload,swapFin,swapEquiv,
          swapAt,swapHeldFin,swapHeldAt]
      · have he : c ≠ ⟨S.carrier v,hc⟩ := fun he => h (congrArg Subtype.val he)
        simp [bodyPartition,payloadPartition,restrictPayload,swapFin,swapEquiv,
          swapAt,swapHeldFin,swapHeldAt,Function.update_of_ne h,Function.update_of_ne he]
  · funext c
    have h : c.val ≠ S.carrier v := by
      intro he
      exact Finset.mem_compl.mp c.property (he ▸ hc)
    simp [bodyPartition,payloadPartition,restrictPayload,swapFin,swapEquiv,
      swapAt,Function.update_of_ne h]

/-- The first device cut after the arrival event, not the cut before arrival. -/
def arrivalCut {I : Inventory} {S : Schedule I} (v : Fin S.visits) : Cut S :=
  ⟨(S.position (v,false)).val + 1, by
    have h := S.ordered v
    have hbound := (S.position (v,true)).isLt
    omega⟩

theorem carrier_held_at_arrival {I : Inventory} {S : Schedule I} (v : Fin S.visits) :
    S.carrier v ∈ held S (arrivalCut v) := by
  simp only [held,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨v,rfl,?_,?_⟩
  · simp [arrivalCut]
  · exact S.ordered v

theorem arrivalCut_injective {I : Inventory} {S : Schedule I} :
    Function.Injective (arrivalCut (S := S)) := by
  intro v w h
  have hv := congrArg Fin.val h
  have he : S.position (v,false) = S.position (w,false) := Fin.ext (by
    simpa [arrivalCut] using hv)
  exact congrArg Prod.fst (S.position.injective he)

def gate {I : Inventory} {S : Schedule I} (k : Cut S) :
    Mat (Fin (Fintype.card (Stock S)) × Payload I) :=
  if h : ∃ v, arrivalCut v = k then (swapFin (Classical.choose h)).permMatrix ℂ else 1

theorem gate_arrival {I : Inventory} {S : Schedule I} (v : Fin S.visits) :
    gate (arrivalCut v) = (swapFin v).permMatrix ℂ := by
  have h : ∃ w, arrivalCut w = arrivalCut v := ⟨v,rfl⟩
  rw [gate,dif_pos h]
  have he := arrivalCut_injective (Classical.choose_spec h)
  rw [he]

theorem gate_elsewhere {I : Inventory} {S : Schedule I} (k : Cut S)
    (h : ∀ v, arrivalCut v ≠ k) : gate k = 1 := by
  simp [gate,not_exists.mpr h]

theorem gate_unitary {I : Inventory} {S : Schedule I} (k : Cut S) :
    IsUnitary (gate k) := by
  unfold gate
  split_ifs
  · exact permutation_unitary _
  · constructor <;> simp

theorem gate_local {I : Inventory} {S : Schedule I} (k : Cut S) :
    LocalOn I (Fintype.card (Stock S)) (held S k) (gate k) := by
  by_cases h : ∃ v, arrivalCut v = k
  · obtain ⟨v,rfl⟩ := h
    rw [gate_arrival]
    exact swapFin_local v _ (carrier_held_at_arrival v)
  · rw [gate_elsewhere k (not_exists.mp h)]
    simpa only [permMatrix_refl] using
      local_permutation I (Fintype.card (Stock S)) (held S k)
        (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)

def initialVector {I : Inventory} (S : Schedule I) : Fin (Fintype.card (Stock S)) → ℂ :=
  fun i => epr ((stockFin S).symm i)

theorem initialVector_normalized {I : Inventory} (S : Schedule I) :
    ∑ i, Complex.normSq (initialVector S i) = 1 := by
  simp only [initialVector]
  exact (Equiv.sum_comp (stockFin S).symm
    (fun x => Complex.normSq (epr x))).trans epr_normalized

def source {I : Inventory} (S : Schedule I) : Density (Fin (Fintype.card (Stock S))) where
  matrix := pureMatrix (initialVector S)
  positive := pureMatrix_positive _
  normalized := by rw [pureMatrix_trace,initialVector_normalized,Complex.ofReal_one]

/-- A concrete legal recorder. Its body consists of all visit registers and
their partners; there is no discarded register or implicit bath. -/
def extension {I : Inventory} (S : Schedule I) : Extension S where
  b := Fintype.card (Stock S)
  b_pos := Fintype.card_pos
  source := source S
  f := 1
  f_pos := Nat.zero_lt_one
  purification := fun x => initialVector S x.1
  purification_norm := by
    simpa only [Fintype.sum_prod_type,Fin.sum_univ_one] using initialVector_normalized S
  purification_reduces := by
    ext i j
    simp [partialRight,pureMatrix,source]
  gate := gate
  unitary := gate_unitary
  gate_local := gate_local

theorem extension_arrival {I : Inventory} (S : Schedule I) (v : Fin S.visits) :
    (extension S).gate (arrivalCut v) = (swapFin v).permMatrix ℂ := gate_arrival v

theorem extension_elsewhere {I : Inventory} (S : Schedule I) (k : Cut S)
    (h : ∀ v, arrivalCut v ≠ k) : (extension S).gate k = 1 := gate_elsewhere k h

theorem source_exact {I : Inventory} (S : Schedule I) :
    (source S).matrix.submatrix (stockFin S) (stockFin S) =
      pureMatrix (epr (a := Inputs S)) := by
  ext i j
  simp [source,initialVector,pureMatrix]

theorem source_input_flat {I : Inventory} (S : Schedule I) :
    partialRight ((source S).matrix.submatrix (stockFin S) (stockFin S)) =
      diagonal (fun _ => ((Fintype.card (Inputs S) : ℝ)⁻¹ : ℂ)) := by
  rw [source_exact,epr_reduction]

/-- Every matrix entry, including off-diagonal coherences against an arbitrary
reference, is transported by the actual full SWAP permutation. -/
theorem swap_reference_evolve {I : Inventory} {S : Schedule I}
    (v : Fin S.visits) {z : Type} [Fintype z] [DecidableEq z]
    (ρ : Mat ((Stock S × Payload I) × z)) (i j : (Stock S × Payload I) × z) :
    evolve (Equiv.Perm.permMatrix ℂ (Equiv.prodCongr (swapEquiv v) (Equiv.refl z))) ρ i j =
      ρ (swapAt v i.1,i.2) (swapAt v j.1,j.2) := by
  rw [permutation_evolve]
  rfl

/-- A second visit of the same physical carrier uses a different retained
register, leaving the first visit's stored input untouched. -/
theorem returned_loan_fresh {I : Inventory} {S : Schedule I}
    (v w : Fin S.visits) (hvw : v ≠ w) (_hc : S.carrier v = S.carrier w)
    (x : Stock S × Payload I) :
    (swapAt w x).1.1 v = x.1.1 v ∧ (swapAt w x).1.1 w = x.2 (S.carrier w) :=
  ⟨swapAt_other_input w v hvw x,swapAt_input w x⟩

/-- Expose a single fresh pair and an arbitrary incoming reference system. -/
def pairSwap {a z : Type} : Equiv.Perm ((a × a) × (a × z)) where
  toFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  invFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem pair_transfer_entry {a z : Type} [Fintype a] [Fintype z]
    [DecidableEq a] [DecidableEq z] (σ : Mat (a × z))
    (i j : (a × a) × (a × z)) :
    evolve ((pairSwap (a := a) (z := z)).permMatrix ℂ)
      (pureMatrix epr ⊗ₖ σ) i j =
      σ (i.1.1,i.2.2) (j.1.1,j.2.2) * epr (i.2.1,i.1.2) *
        star (epr (j.2.1,j.1.2)) := by
  rw [permutation_evolve]
  change (epr (i.2.1,i.1.2) * star (epr (j.2.1,j.1.2))) *
    σ (i.1.1,i.2.2) (j.1.1,j.2.2) = _
  ring

/-- Tracing the EPR partner and outgoing carrier leaves exactly the incoming
joint state of stored input and reference; no input independence is assumed. -/
theorem pair_stores_input_reference {a z : Type} [Fintype a] [Fintype z]
    [DecidableEq a] [DecidableEq z] [Nonempty a] (σ : Mat (a × z)) (i j : a × z) :
    (∑ r : a, ∑ p : a,
      evolve ((pairSwap (a := a) (z := z)).permMatrix ℂ)
        (pureMatrix epr ⊗ₖ σ) ((i.1,r),(p,i.2)) ((j.1,r),(p,j.2))) = σ i j := by
  simp_rw [pair_transfer_entry,mul_assoc]
  change (∑ r : a, ∑ p : a, σ i j * (epr (p,r) * starRingEnd ℂ (epr (p,r)))) = _
  simp_rw [Complex.mul_conj,← Finset.mul_sum,← Complex.ofReal_sum]
  have he : (∑ r : a, ∑ p : a, Complex.normSq (epr (p,r))) = 1 := by
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using (epr_normalized (a := a))
  rw [he,Complex.ofReal_one,mul_one]

/-- The physical outgoing carrier and retained partner are precisely the fresh
EPR pair after the transfer, including for mixed correlated incoming states. -/
theorem pair_releases_epr {a z : Type} [Fintype a] [Fintype z]
    [DecidableEq a] [DecidableEq z] (σ : Density (a × z)) (i j : a × a) :
    (∑ x : a, ∑ k : z,
      evolve ((pairSwap (a := a) (z := z)).permMatrix ℂ)
        (pureMatrix epr ⊗ₖ σ.matrix) ((x,i.2),(i.1,k)) ((x,j.2),(j.1,k))) =
      pureMatrix epr i j := by
  simp_rw [pair_transfer_entry,← Finset.sum_mul]
  have he : (∑ x : a, ∑ k : z, σ.matrix (x,k) (x,k)) = 1 := by
    simpa only [Matrix.trace,Fintype.sum_prod_type] using σ.normalized
  rw [he,one_mul]
  rfl

def globalSwap {I : Inventory} {S : Schedule I} (v : Fin S.visits) (r : ℕ) :
    Equiv.Perm (Global (extension S) r) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodCongr (swapFin v) (Equiv.refl (Fin r))).trans (Equiv.prodAssoc _ _ _))

/-- The actual device matrix at an arrival, lifted by the identity on tester
memory, transports every global matrix entry by the fresh-visit SWAP. -/
theorem device_reference_evolve {I : Inventory} (S : Schedule I)
    (v : Fin S.visits) (r : ℕ) (ρ : Mat (Global (extension S) r)) :
    evolve (fun i j : Global (extension S) r =>
      (extension S).gate (arrivalCut v) (i.1,i.2.1) (j.1,j.2.1) *
        if i.2.2 = j.2.2 then 1 else 0) ρ =
      ρ.submatrix (globalSwap v r) (globalSwap v r) := by
  have he : (fun i j : Global (extension S) r =>
      (extension S).gate (arrivalCut v) (i.1,i.2.1) (j.1,j.2.1) *
        if i.2.2 = j.2.2 then 1 else 0) = (globalSwap v r).permMatrix ℂ := by
    ext i j
    rw [extension_arrival,permutation_entry,permutation_entry]
    have hiff : globalSwap v r i = j ↔
        swapFin v (i.1,i.2.1) = (j.1,j.2.1) ∧ i.2.2 = j.2.2 := by
      change (Equiv.prodAssoc _ _ _) (swapFin v (i.1,i.2.1),i.2.2) = j ↔ _
      rw [Equiv.apply_eq_iff_eq_symm_apply,Prod.mk.injEq]
      rfl
    by_cases ha : swapFin v (i.1,i.2.1) = (j.1,j.2.1)
    · by_cases hr : i.2.2 = j.2.2
      · have hg := hiff.mpr ⟨ha,hr⟩
        simp only [if_pos ha,if_pos hr,if_pos hg,mul_one]
      · have hg : globalSwap v r i ≠ j := fun h => hr (hiff.mp h).2
        simp only [if_pos ha,if_neg hr,if_neg hg,mul_zero]
    · have hg : globalSwap v r i ≠ j := fun h => ha (hiff.mp h).1
      simp only [if_neg ha,if_neg hg,zero_mul]
  rw [he,permutation_evolve]

end Recorder
end ScheduleLaw
