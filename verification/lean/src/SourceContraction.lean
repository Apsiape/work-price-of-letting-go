import WireTensor

/-! The actual initialized source contraction, including every off-diagonal
source-purifier block and the entire tester/reference state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History.Wire

def crossOuter {a b : Type} (v : a → ℂ) (w : b → ℂ) : Matrix a b ℂ :=
  fun i j => v i * star (w j)

theorem cross_outer_transform {a b d : Type} [Fintype a]
    (K : Matrix b a ℂ) (L : Matrix d a ℂ) (v w : a → ℂ) :
    K * crossOuter v w * Lᴴ = crossOuter (K *ᵥ v) (L *ᵥ w) := by
  ext i j
  simp only [crossOuter,mulVec,dotProduct,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_sum,star_mul,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem cross_outer_normalized {a b : Type} [Fintype a] (v : b → ℂ) (w : a → ℂ)
    (hw : ∑ j, Complex.normSq (w j) = 1) : crossOuter v w *ᵥ w = v := by
  ext i
  change (∑ j, (v i * star (w j)) * w j) = v i
  have he (j : a) : (v i * star (w j)) * w j = v i * (Complex.normSq (w j) : ℂ) := by
    calc (v i * star (w j)) * w j = v i * (w j * star (w j)) := by ring
      _ = _ := by rw [Complex.star_def,Complex.mul_conj]
  simp_rw [he]
  rw [← Finset.mul_sum,← Complex.ofReal_sum,hw,Complex.ofReal_one,mul_one]

def sourceKernel {I : Inventory} {S : Schedule I} (e : Extension S) (f : Fin e.f) :
    Matrix (Fin e.b) (Recorder.Stock S) ℂ :=
  crossOuter (fun i => e.purification (i,f)) Recorder.epr

theorem sourceKernel_initial_cross {I : Inventory} {S : Schedule I} (e : Extension S)
    (f g : Fin e.f) : sourceKernel e f * pureMatrix (Recorder.epr (a := Recorder.Inputs S)) *
      (sourceKernel e g)ᴴ = crossOuter (fun i => e.purification (i,f)) (fun i => e.purification (i,g)) := by
  change sourceKernel e f * crossOuter (Recorder.epr (a := Recorder.Inputs S)) Recorder.epr *
    (sourceKernel e g)ᴴ = _
  rw [cross_outer_transform]
  unfold sourceKernel
  rw [cross_outer_normalized _ _ Recorder.epr_normalized,cross_outer_normalized _ _ Recorder.epr_normalized]

theorem raw_initial_product {I : Inventory} (S : Schedule I) {r : ℕ} (t : Tester S r) :
    rawState t 0 = pureMatrix (Recorder.epr (a := Recorder.Inputs S)) ⊗ₖ initialTesterMatrix t := by
  unfold rawState
  rw [run_amplitudes]
  ext i j
  simp only [amplitudes,pureMatrix,initialTesterMatrix,kroneckerMap_apply,star_mul]
  ring

def sourceCrossInitial {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (f g : Fin e.f) : Mat (Global e r) :=
  crossOuter (fun i => e.purification (i,f)) (fun i => e.purification (i,g)) ⊗ₖ initialTesterMatrix t

theorem source_initial_contraction {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (f g : Fin e.f) :
    (sourceKernel e f ⊗ₖ (1 : Mat (Payload I × Fin r))) * rawState t 0 *
      (sourceKernel e g ⊗ₖ (1 : Mat (Payload I × Fin r)))ᴴ = sourceCrossInitial e t f g := by
  rw [raw_initial_product,conjTranspose_kronecker,← mul_kronecker_mul,← mul_kronecker_mul]
  simp only [conjTranspose_one,one_mul,mul_one,sourceKernel_initial_cross]
  rfl

theorem source_purified_initial_contraction {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (f g : Fin e.f) (i j : Global e r) :
    pureMatrix (purifiedInitial e t) (i,f) (j,g) =
      ((sourceKernel e f ⊗ₖ (1 : Mat (Payload I × Fin r))) * rawState t 0 *
        (sourceKernel e g ⊗ₖ (1 : Mat (Payload I × Fin r)))ᴴ) i j := by
  rw [source_initial_contraction]
  simp only [pureMatrix,purifiedInitial,sourceCrossInitial,crossOuter,initialTesterMatrix,
    kroneckerMap_apply,star_mul]
  ring

theorem source_diagonal_reconstruction {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : initialState e t = ∑ f, sourceCrossInitial e t f f := by
  ext i j
  have hp := congrFun₂ e.purification_reduces i.1 j.1
  change (∑ f, e.purification (i.1,f) * star (e.purification (j.1,f))) = e.source.matrix i.1 j.1 at hp
  simp only [initialState,sourceCrossInitial,crossOuter,Matrix.sum_apply,kroneckerMap_apply]
  rw [← hp,Finset.sum_mul]
  rfl

end ScheduleLaw.History.Wire
