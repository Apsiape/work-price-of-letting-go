import GibbsAccounting
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw

def payloadPartition (I : Inventory) (A : Finset (Fin I.count)) :
    Payload I ≃ Restricted I A × Restricted I Aᶜ where
  toFun p := (restrictPayload I A p,restrictPayload I Aᶜ p)
  invFun p c := if h : c ∈ A then p.1 ⟨c,h⟩ else p.2 ⟨c,Finset.mem_compl.mpr h⟩
  left_inv p := by
    funext c
    by_cases hc : c ∈ A <;> simp [hc,restrictPayload]
  right_inv p := by
    rcases p with ⟨p,q⟩
    apply Prod.ext
    · funext c
      simp [restrictPayload,c.property]
    · funext c
      simp [restrictPayload,Finset.mem_compl.mp c.property]

def bodyPartition (I : Inventory) (b : ℕ) (A : Finset (Fin I.count)) :
    (Fin b × Payload I) ≃ (Fin b × Restricted I A) × Restricted I Aᶜ :=
  (Equiv.prodCongr (Equiv.refl (Fin b)) (payloadPartition I A)).trans
    (Equiv.prodAssoc (Fin b) (Restricted I A) (Restricted I Aᶜ)).symm

def externalObservable (I : Inventory) (b : ℕ) (A : Finset (Fin I.count))
    (H : Mat (Restricted I Aᶜ)) : Mat (Fin b × Payload I) :=
  ((1 : Mat (Fin b × Restricted I A)) ⊗ₖ H).submatrix
    (bodyPartition I b A) (bodyPartition I b A)

theorem local_conserves_external (I : Inventory) (b : ℕ)
    (A : Finset (Fin I.count)) (U : Mat (Fin b × Payload I))
    (hU : LocalOn I b A U) (H : Mat (Restricted I Aᶜ)) :
    Conserves U (externalObservable I b A H) := by
  obtain ⟨V,hV,hUV⟩ := hU
  have he : U = (V ⊗ₖ (1 : Mat (Restricted I Aᶜ))).submatrix
      (bodyPartition I b A) (bodyPartition I b A) := by
    ext i j
    rw [hUV]
    rfl
  rw [he]
  unfold Conserves externalObservable
  rw [conjTranspose_submatrix,submatrix_mul_equiv,submatrix_mul_equiv,
    conjTranspose_kronecker,← mul_kronecker_mul,← mul_kronecker_mul]
  simp only [conjTranspose_one,mul_one,one_mul,hV.1]

def carrierObservable (I : Inventory) (b : ℕ) (c : Fin I.count) :
    Mat (Fin b × Payload I) := fun i j =>
  (if i.1 = j.1 ∧ (∀ d, d ≠ c → i.2 d = j.2 d) then 1 else 0) *
    (I.H c).matrix (i.2 c) (j.2 c)

theorem other_coordinates_partition (I : Inventory) (A : Finset (Fin I.count))
    (c : Fin I.count) (hc : c ∉ A) (p q : Payload I) :
    (∀ d, d ≠ c → p d = q d) ↔
      restrictPayload I A p = restrictPayload I A q ∧
        (∀ d : {d // d ∈ Aᶜ}, d.val ≠ c → p d.val = q d.val) := by
  constructor
  · intro h
    constructor
    · funext d
      apply h d.val
      intro he
      exact hc (he ▸ d.property)
    · intro d hd
      exact h d.val hd
  · rintro ⟨hA,hB⟩ d hd
    by_cases h : d ∈ A
    · exact congrFun hA ⟨d,h⟩
    · exact hB ⟨d,Finset.mem_compl.mpr h⟩ hd

theorem local_conserves_unheld_carrier (I : Inventory) (b : ℕ)
    (A : Finset (Fin I.count)) (U : Mat (Fin b × Payload I))
    (hU : LocalOn I b A U) (c : Fin I.count) (hc : c ∉ A) :
    Conserves U (carrierObservable I b c) := by
  let H : Mat (Restricted I Aᶜ) := fun p q =>
    (if ∀ d : {d // d ∈ Aᶜ}, d.val ≠ c → p d = q d then 1 else 0) *
      (I.H c).matrix (p ⟨c,Finset.mem_compl.mpr hc⟩) (q ⟨c,Finset.mem_compl.mpr hc⟩)
  have he : carrierObservable I b c = externalObservable I b A H := by
    ext i j
    have hp := other_coordinates_partition I A c hc i.2 j.2
    simp only [externalObservable,submatrix_apply,kroneckerMap_apply,one_apply,
      bodyPartition,Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.prodAssoc_symm_apply,
      payloadPartition,carrierObservable,H,restrictPayload]
    by_cases hb : i.1 = j.1 <;>
      by_cases ha : restrictPayload I A i.2 = restrictPayload I A j.2 <;>
      by_cases hz : ∀ d : {d // d ∈ Aᶜ}, d.val ≠ c → i.2 d.val = j.2 d.val <;>
      simp_all [Prod.mk.injEq,restrictPayload]
  rw [he]
  exact local_conserves_external I b A U hU H

def matrixBlock {a b : Type} (ρ : Mat (a × b)) (i j : a) : Mat b :=
  fun k l => ρ (i,k) (j,l)

theorem block_evolve_one_kron {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (V : Mat b) (ρ : Mat (a × b)) (i j : a) :
    matrixBlock (evolve ((1 : Mat a) ⊗ₖ V) ρ) i j = evolve V (matrixBlock ρ i j) := by
  ext k l
  simp only [matrixBlock,evolve,Matrix.mul_apply,Fintype.sum_prod_type,
    kroneckerMap_apply,one_apply,conjTranspose_apply,apply_ite]
  simp only [ite_mul,zero_mul,mul_ite,mul_zero,map_zero]
  simp [apply_ite,Finset.sum_ite_irrel]

theorem evolve_trace {a : Type} [Fintype a] [DecidableEq a]
    (V ρ : Mat a) (hV : IsUnitary V) : (evolve V ρ).trace = ρ.trace := by
  unfold evolve
  rw [trace_mul_cycle,hV.1,one_mul]

theorem partialRight_evolve_one_kron {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (V : Mat b) (ρ : Mat (a × b))
    (hV : IsUnitary V) : partialRight (evolve ((1 : Mat a) ⊗ₖ V) ρ) = partialRight ρ := by
  ext i j
  change (matrixBlock (evolve ((1 : Mat a) ⊗ₖ V) ρ) i j).trace =
    (matrixBlock ρ i j).trace
  rw [block_evolve_one_kron,evolve_trace V _ hV]

theorem evolve_submatrix_equiv {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (U ρ : Mat b) :
    evolve (U.submatrix e e) (ρ.submatrix e e) = (evolve U ρ).submatrix e e := by
  simp [evolve,conjTranspose_submatrix,submatrix_mul_equiv]

theorem partialLeft_swap {a b : Type} [Fintype a] [Fintype b] (ρ : Mat (a × b)) :
    partialLeft ρ = partialRight (ρ.submatrix (Equiv.prodComm b a) (Equiv.prodComm b a)) := rfl

theorem kron_swap {a b : Type} (A : Mat a) (B : Mat b) :
    (A ⊗ₖ B).submatrix (Equiv.prodComm b a) (Equiv.prodComm b a) = B ⊗ₖ A := by
  ext i j
  simp [kroneckerMap_apply,mul_comm]

theorem partialLeft_evolve_kron_one {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (U : Mat a) (ρ : Mat (a × b))
    (hU : IsUnitary U) : partialLeft (evolve (U ⊗ₖ (1 : Mat b)) ρ) = partialLeft ρ := by
  rw [partialLeft_swap,← evolve_submatrix_equiv,kron_swap,
    partialRight_evolve_one_kron _ _ hU]
  rfl

theorem active_visit_unique {I : Inventory} (S : Schedule I) (k : Cut S)
    {v w : Fin S.visits} (hv : (S.position (v,false)).val < k.val ∧
      k.val ≤ (S.position (v,true)).val)
    (hw : (S.position (w,false)).val < k.val ∧ k.val ≤ (S.position (w,true)).val)
    (hc : S.carrier v = S.carrier w) : v = w := by
  by_contra hne
  rcases S.disjoint v w hne hc with h | h
  · have hh := h
    change (S.position (v,true)).val < (S.position (w,false)).val at hh
    omega
  · have hh := h
    change (S.position (w,true)).val < (S.position (v,false)).val at hh
    omega

theorem sum_active_visits {I : Inventory} (S : Schedule I) (k : Cut S)
    (f : Fin I.count → ℝ) :
    (∑ v ∈ Finset.univ.filter (fun v : Fin S.visits =>
      (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val), f (S.carrier v)) =
      ∑ c ∈ held S k, f c := by
  apply Finset.sum_bij (fun v _ => S.carrier v)
  · intro v hv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
    simp only [held,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨v,rfl,hv⟩
  · intro v hv w hw hc
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv hw
    exact active_visit_unique S k hv hw hc
  · intro c hc
    simp only [held,Finset.mem_filter,Finset.mem_univ,true_and] at hc
    obtain ⟨v,hv,hk⟩ := hc
    exact ⟨v,by simpa using hk,hv⟩
  · intro v hv
    rfl

theorem visit_telescope {I : Inventory} (S : Schedule I) (v : Fin S.visits)
    (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Ico ((S.position (v,false)).val+1) ((S.position (v,true)).val+1),
      (f (k+1)-f k)) = f ((S.position (v,true)).val+1) - f ((S.position (v,false)).val+1) := by
  apply Finset.sum_Ico_sub
  have h := S.ordered v
  change (S.position (v,false)).val < (S.position (v,true)).val at h
  omega

theorem visit_telescope_fin {I : Inventory} (S : Schedule I) (v : Fin S.visits)
    (f : ℕ → ℝ) :
    (∑ k : Cut S, if (S.position (v,false)).val < k.val ∧
      k.val ≤ (S.position (v,true)).val then (f (k.val+1)-f k.val) else 0) =
      f ((S.position (v,true)).val+1) - f ((S.position (v,false)).val+1) := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if (S.position (v,false)).val < n ∧
    n ≤ (S.position (v,true)).val then f (n+1)-f n else 0) (2*S.visits+1),
    ← Finset.sum_filter]
  have he : (Finset.range (2*S.visits+1)).filter (fun k =>
      (S.position (v,false)).val < k ∧ k ≤ (S.position (v,true)).val) =
      Finset.Ico ((S.position (v,false)).val+1) ((S.position (v,true)).val+1) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    have hr := (S.position (v,true)).isLt
    omega
  rw [he,visit_telescope]

theorem schedule_energy_telescope {I : Inventory} (S : Schedule I)
    (f : ℕ → ℝ) (g : Fin I.count → ℕ → ℝ)
    (hstep : ∀ k : Cut S, (f (k.val+1)-f k.val) +
      (∑ c ∈ held S k,(g c (k.val+1)-g c k.val)) = 0) :
    f (2*S.visits+1)-f 0 +
      (∑ v, (g (S.carrier v) ((S.position (v,true)).val+1) -
        g (S.carrier v) ((S.position (v,false)).val+1))) = 0 := by
  have hf : (∑ k : Cut S,(f (k.val+1)-f k.val)) = f (2*S.visits+1)-f 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n+1)-f n) (2*S.visits+1),← Nat.Ico_zero_eq_range]
    apply Finset.sum_Ico_sub
    omega
  have hg : (∑ k : Cut S,∑ c ∈ held S k,(g c (k.val+1)-g c k.val)) =
      ∑ v,(g (S.carrier v) ((S.position (v,true)).val+1) -
        g (S.carrier v) ((S.position (v,false)).val+1)) := by
    calc
      _ = ∑ k : Cut S,∑ v : Fin S.visits,
          if (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val
          then g (S.carrier v) (k.val+1)-g (S.carrier v) k.val else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← sum_active_visits S k (fun c => (g c (k.val+1)-g c k.val)),Finset.sum_filter]
      _ = ∑ v : Fin S.visits,∑ k : Cut S,
          if (S.position (v,false)).val < k.val ∧ k.val ≤ (S.position (v,true)).val
          then g (S.carrier v) (k.val+1)-g (S.carrier v) k.val else 0 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun v _ => visit_telescope_fin S v (g (S.carrier v)))
  have hsum : (∑ k : Cut S,(f (k.val+1)-f k.val)) +
      (∑ k : Cut S,∑ c ∈ held S k,(g c (k.val+1)-g c k.val)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun k _ => hstep k)
  rwa [hf,hg] at hsum

end ScheduleLaw
