import RecordCausality
import QuantumEntropyAdapter

/-! A pure marginal factors from the complete pure state, with no independence
assumption on the remaining registers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Braket
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace History

def ketOfVector {a : Type} [Fintype a] (v : a → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) : Ket a :=
  ⟨v,by simpa only [Complex.normSq_eq_norm_sq] using hv⟩

theorem library_pure_matrix {a : Type} [Fintype a] [DecidableEq a] (ψ : Ket a) :
    (MState.pure ψ).m = pureMatrix ψ.vec := by
  ext i j
  change ψ.vec i * starRingEnd ℂ (ψ.vec j) = ψ.vec i * star (ψ.vec j)
  rfl

/-- A rank-one normalized left marginal implies exact factorization against
the entire right system, including arbitrary observer references. -/
theorem pure_marginal_factor {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (ψ : a × b → ℂ) (φ : a → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1)
    (hφ : ∑ x, Complex.normSq (φ x) = 1)
    (hm : partialRight (pureMatrix ψ) = pureMatrix φ) :
    pureMatrix ψ = pureMatrix φ ⊗ₖ partialLeft (pureMatrix ψ) := by
  let ξ : Ket (b × a) := ketOfVector (fun x => ψ (x.2,x.1)) (by
    exact (Equiv.sum_comp (Equiv.prodComm b a) (fun x => Complex.normSq (ψ x))).trans hψ)
  let ζ : Ket a := ketOfVector φ hφ
  have hp : MState.pure ζ = (MState.pure ξ).traceLeft := by
    apply MState.ext_m
    change (MState.pure ζ).m = partialLeft (MState.pure ξ).m
    rw [library_pure_matrix,library_pure_matrix]
    ext i j
    exact (congrFun (congrFun hm i) j).symm
  have hs := (MState.pure_separable_iff_traceLeft_pure ξ).mpr ⟨ζ,hp⟩
  obtain ⟨η,θ,hξ⟩ := (MState.pure_separable_iff_IsProd ξ).mp hs
  have he (i : a) (j : b) : ψ (i,j) = η.vec j * θ.vec i := by
    have h := congrArg (fun k : Ket (b × a) => k.vec (j,i)) hξ
    exact h
  have ht : pureMatrix ψ = pureMatrix θ.vec ⊗ₖ pureMatrix η.vec := by
    ext i j
    simp only [pureMatrix,he,kroneckerMap_apply,star_mul]
    ring
  have hη : (pureMatrix η.vec).trace = 1 := by
    have hn : ∑ i, Complex.normSq (η.vec i) = 1 := by simpa only [Ket.coe_fun_eq] using η.normalized
    rw [pureMatrix_trace,hn,Complex.ofReal_one]
  have hθ : (pureMatrix θ.vec).trace = 1 := by
    have hn : ∑ i, Complex.normSq (θ.vec i) = 1 := by simpa only [Ket.coe_fun_eq] using θ.normalized
    rw [pureMatrix_trace,hn,Complex.ofReal_one]
  have hleft : partialLeft (pureMatrix ψ) = pureMatrix η.vec := by
    rw [ht,partialLeft_kron,hθ,one_smul]
  have hright : pureMatrix φ = pureMatrix θ.vec := by
    rw [← hm,ht,partialRight_kron,hη,one_smul]
  rw [hleft,hright,ht]

end History
end ScheduleLaw
