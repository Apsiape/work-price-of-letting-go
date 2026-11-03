import PrefixIsometry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker
namespace ScheduleLaw.Blueprint

/-- Two isometric embeddings of the same finite register into one fixed
ambient register differ by a full square unitary on that ambient register. -/
theorem isometry_square_completion {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] (J K : Matrix z a ℂ)
    (hJ : Jᴴ*J=1) (hK : Kᴴ*K=1) :
    ∃ U : Mat z, IsUnitary U ∧ U*J=K := by
  have hJt : Jᵀ*Jᵀᴴ=1 := by
    ext i j
    have h := congrFun₂ hJ i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.one_apply, map_sum, star_mul, mul_comm] using congrArg star h
  have hKt : Kᵀ*Kᵀᴴ=1 := by
    ext i j
    have h := congrFun₂ hK i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.one_apply, map_sum, star_mul, mul_comm] using congrArg star h
  obtain ⟨U,hU,hfactor⟩ := History.gram_factor_isometry Jᵀ Kᵀ (hJt.trans hKt.symm) le_rfl
  refine ⟨U,⟨hU,mul_eq_one_comm.mp hU⟩,?_⟩
  have ht := congrArg Matrix.transpose hfactor
  simpa only [transpose_mul, transpose_transpose] using ht.symm

/-- A rectangular burst isometry can be completed after the incoming and
outgoing memory/port registers have both been embedded in the same space. -/
theorem embedded_burst_square_completion {a b z : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype z] [DecidableEq z]
    (V : Matrix b a ℂ) (J : Matrix z a ℂ) (K : Matrix z b ℂ)
    (hV : Vᴴ*V=1) (hJ : Jᴴ*J=1) (hK : Kᴴ*K=1) :
    ∃ U : Mat z, IsUnitary U ∧ U*J=K*V := by
  apply isometry_square_completion J (K*V) hJ
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K V,
    hK, Matrix.one_mul, hV]

def registerEmbedding {a z : Type} [DecidableEq z] (f : a ↪ z) : Matrix z a ℂ :=
  fun i j => if i=f j then 1 else 0

theorem registerEmbedding_isometry {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] (f : a ↪ z) :
    (registerEmbedding f)ᴴ * registerEmbedding f = 1 := by
  ext i j
  simp [registerEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, ite_mul, f.injective.eq_iff, eq_comm]

theorem isometric_embedding_of_card_le {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] (h : Fintype.card a ≤ Fintype.card z) :
    ∃ J : Matrix z a ℂ, Jᴴ*J=1 := by
  let f : a ↪ z := {
    toFun := fun x => (Fintype.equivFin z).symm (Fin.castLE h (Fintype.equivFin a x))
    inj' := (Fintype.equivFin z).symm.injective.comp
      ((Fin.castLE_injective h).comp (Fintype.equivFin a).injective) }
  exact ⟨registerEmbedding f,registerEmbedding_isometry f⟩

/-- The canonical purification step is realized by one full square gate
after fixing isometric embeddings of its incoming and padded outgoing spaces. -/
theorem canonical_prefix_square_completion {I : Inventory} {S : Schedule I}
    (Z : History.PrefixMatrices S) (hZ : History.IsCausalPrefixFamily S Z)
    (b : History.InputBurst S) (hb : 0 < (History.inputRank b).val)
    {z : Type} [Fintype z] [DecidableEq z]
    (J : Matrix z (History.PrefixSpace (History.previousInput b hb) × History.BurstOutputs b hb) ℂ)
    (K : Matrix z (History.BurstInputs b hb × (History.PrefixSpace b ⊕
      (History.PrefixSpace (History.previousInput b hb) × History.BurstOutputs b hb))) ℂ)
    (hJ : Jᴴ*J=1) (hK : Kᴴ*K=1) :
    ∃ U : Mat z, IsUnitary U ∧ ∀ x o w,
      (∑ m, History.previousPrefixAmplitude Z hZ b hb x m * (U*J) w (m,o)) =
      ∑ a, History.paddedBurstAmplitude
        (m := History.PrefixSpace (History.previousInput b hb))
        (History.currentPrefixAmplitude Z hZ b hb) (x,o) a * K w a := by
  obtain ⟨V,hV,hAmp⟩ := History.canonical_prefix_burst_isometry Z hZ b hb
  obtain ⟨U,hU,hUJ⟩ := embedded_burst_square_completion V J K hV hJ hK
  refine ⟨U,hU,?_⟩
  intro x o w
  have hAmp' (a) : History.paddedBurstAmplitude
      (m := History.PrefixSpace (History.previousInput b hb))
      (History.currentPrefixAmplitude Z hZ b hb) (x,o) a =
      ∑ m, History.previousPrefixAmplitude Z hZ b hb x m * V a (m,o) :=
    hAmp x o a.1 a.2
  simp_rw [hUJ, Matrix.mul_apply, Finset.mul_sum, hAmp', Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro m _
  ring

def localRegisterGate (I : Inventory) (r : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Fin r × Restricted I A)) : Mat (Fin r × Payload I) :=
  (U ⊗ₖ (1 : Mat (Restricted I Aᶜ))).submatrix (bodyPartition I r A) (bodyPartition I r A)

theorem localRegisterGate_unitary (I : Inventory) (r : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Fin r × Restricted I A)) (hU : IsUnitary U) :
    IsUnitary (localRegisterGate I r A U) := by
  apply unitary_submatrix
  apply unitary_kron hU
  constructor <;> simp

theorem localRegisterGate_local (I : Inventory) (r : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Fin r × Restricted I A)) (hU : IsUnitary U) :
    LocalOn I r A (localRegisterGate I r A U) := by
  exact ⟨U,hU,fun _ _ => rfl⟩

/-- A single fixed finite memory and local square gates give a lawful Tester
in the original carrier-inventory model. Prefix matching is a separate claim. -/
def testerOfLocalGates {I : Inventory} (S : Schedule I) (r : ℕ)
    (ψ : Fin r × Payload I → ℂ) (hψ : ∑ x, Complex.normSq (ψ x)=1)
    (U : (k : Cut S) → Mat (Fin r × Restricted I (held S k)ᶜ))
    (hU : ∀ k, IsUnitary (U k)) : Tester S r where
  initial := ψ
  normalized := hψ
  gate k := localRegisterGate I r (held S k)ᶜ (U k)
  unitary k := localRegisterGate_unitary I r _ (U k) (hU k)
  gate_local k := localRegisterGate_local I r _ (U k) (hU k)

end ScheduleLaw.Blueprint
