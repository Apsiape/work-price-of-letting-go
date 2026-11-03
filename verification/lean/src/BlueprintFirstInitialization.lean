import BlueprintTesterAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem isometry_preserves_normSq {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] (J : Matrix z a ℂ) (hJ : Jᴴ*J=1) (v : a → ℂ) :
    ∑ x,Complex.normSq ((J*ᵥv) x) = ∑ x,Complex.normSq (v x) := by
  have ht := congrArg Matrix.trace (pureMatrix_mulVec J v)
  rw [trace_mul_cycle,hJ,Matrix.one_mul,pureMatrix_trace,pureMatrix_trace] at ht
  exact congrArg Complex.re ht

def firstPrefixPortCoordinates {I : Inventory} {S : Schedule I} (h : 0 < S.visits) :
    PrefixSpace (firstInputBurst S h) ≃ Registers S (inputVisits (firstInputBurst S h)) where
  toFun x := Equiv.cast (congrArg (Registers S) (first_inputs S h)) x.1
  invFun p := ((Equiv.cast (congrArg (Registers S) (first_inputs S h))).symm p,
    fun v => False.elim (by simpa [first_released_empty] using v.property))
  left_inv x := by
    apply Prod.ext
    · exact Equiv.symm_apply_apply _ _
    · funext v
      exact False.elim (by simpa [first_released_empty] using v.property)
  right_inv p := Equiv.apply_symm_apply _ _

/-- Place the first prefix's input ports and purification memory in the
actual carrier inventory. All other carriers start in their zero basis state. -/
def firstPrefixEmbedding {I : Inventory} {S : Schedule I} (h : 0 < S.visits) :
    (PrefixSpace (firstInputBurst S h) × PrefixSpace (firstInputBurst S h)) ↪
      (Fin (burstMemoryDim S) × Payload I) where
  toFun x := (canonicalMemoryEmbedding (firstInputBurst S h) x.2,
    (visitPayloadPartition S (inputVisits (firstInputBurst S h))
      (inputVisits_carriers_injective _)).symm
        (firstPrefixPortCoordinates h x.1,fun c => ⟨0,I.dim_pos c.val⟩))
  inj' := by
    intro x y he
    have hm := (canonicalMemoryEmbedding (firstInputBurst S h)).injective (congrArg Prod.fst he)
    have hp := congrArg (visitPayloadPartition S (inputVisits (firstInputBurst S h))
      (inputVisits_carriers_injective _)) (congrArg Prod.snd he)
    have hi : x.1=y.1 := (firstPrefixPortCoordinates h).injective (by
      simpa only [Equiv.apply_symm_apply] using congrArg Prod.fst hp)
    exact Prod.ext hi hm

theorem firstPrefixEmbedding_selected {I : Inventory} {S : Schedule I} (h : 0 < S.visits)
    (x : PrefixSpace (firstInputBurst S h) × PrefixSpace (firstInputBurst S h))
    (v : {v // v ∈ inputVisits (firstInputBurst S h)}) :
    (firstPrefixEmbedding h x).2 (S.carrier v.val) = firstPrefixPortCoordinates h x.1 v := by
  have hp := congrArg (fun p => p.1 v)
    ((visitPayloadPartition S (inputVisits (firstInputBurst S h))
      (inputVisits_carriers_injective _)).apply_symm_apply
        (firstPrefixPortCoordinates h x.1,fun c => ⟨0,I.dim_pos c.val⟩))
  exact hp

def firstPrefixInitialVector {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0 < S.visits) :
    Fin (burstMemoryDim S) × Payload I → ℂ :=
  registerEmbedding (firstPrefixEmbedding h) *ᵥ prefixPurification S Z hZ (firstInputBurst S h)

theorem firstPrefixInitialVector_normalized {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0 < S.visits) :
    ∑ x,Complex.normSq (firstPrefixInitialVector Z hZ h x)=1 := by
  rw [firstPrefixInitialVector,isometry_preserves_normSq _ (registerEmbedding_isometry _)]
  exact first_prefix_purification_normalized S Z hZ h

theorem firstPrefixInitialVector_at_embedding {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (h : 0 < S.visits)
    (x : PrefixSpace (firstInputBurst S h) × PrefixSpace (firstInputBurst S h)) :
    firstPrefixInitialVector Z hZ h (firstPrefixEmbedding h x) =
      prefixPurification S Z hZ (firstInputBurst S h) x := by
  classical
  simp [firstPrefixInitialVector,Matrix.mulVec,dotProduct,registerEmbedding,
    (firstPrefixEmbedding h).injective.eq_iff]

end ScheduleLaw.Blueprint
