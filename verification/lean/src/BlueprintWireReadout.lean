import BlueprintContracts

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

def terminalCut {I : Inventory} (S : Schedule I) : Cut S := ⟨2*S.visits,by omega⟩

def terminalBodyKernel {I : Inventory} {S : Schedule I} (e : Extension S)
    (K : CutKernel e (terminalCut S)) : Matrix (Fin e.b) (Recorder.Stock S) ℂ :=
  fun i j => K (i,fun c => ⟨0,I.dim_pos c.val⟩) (j,fun c => ⟨0,I.dim_pos c.val⟩)

theorem terminal_kernel_lift {I : Inventory} {S : Schedule I} (e : Extension S)
    (K : CutKernel e (terminalCut S)) (r : ℕ) :
    kernelLift e (terminalCut S) r K = terminalBodyKernel e K ⊗ₖ (1 : Mat (Payload I × Fin r)) := by
  have hheld : held S (terminalCut S)=∅ := held_terminal_empty S
  have hfun (p : Payload I) : restrictPayload I (held S (terminalCut S)) p =
      (fun c : {c // c ∈ held S (terminalCut S)} => ⟨0,I.dim_pos c.val⟩) := by
    funext c
    have hn : ¬(held S (terminalCut S)).Nonempty := by rw [hheld]; simp
    exact False.elim (hn ⟨c.val,c.property⟩)
  have he (p q : Payload I) : restrictPayload I (held S (terminalCut S))ᶜ p =
      restrictPayload I (held S (terminalCut S))ᶜ q ↔ p=q := by
    rw [restriction_eq_iff,hheld]
    simp only [Finset.compl_empty,Finset.mem_univ,true_implies]
    exact funext_iff.symm
  apply Matrix.ext
  intro i j
  simp only [kernelLift,terminalBodyKernel,hfun,he,kroneckerMap_apply,one_apply,Prod.ext_iff]

theorem partialRight_rect_sandwich {a b z : Type} [Fintype a] [Fintype z]
    [DecidableEq z] (K : Matrix b a ℂ) (ρ : Mat (a × z)) :
    partialRight ((K ⊗ₖ (1 : Mat z))*ρ*(K ⊗ₖ (1 : Mat z))ᴴ) = K*partialRight ρ*Kᴴ := by
  have he (i j : b) (k l : z) :
      ((K ⊗ₖ (1 : Mat z))*ρ*(K ⊗ₖ (1 : Mat z))ᴴ) (i,k) (j,l) =
        ∑ y,∑ x, (K i x*ρ (x,k) (y,l))*star (K j y) := by
    simp only [mul_apply,Fintype.sum_prod_type,kroneckerMap_apply,one_apply,conjTranspose_apply]
    simp [apply_ite,mul_ite,ite_mul,Finset.sum_ite_irrel,Finset.sum_mul]
  ext i j
  change (∑ k : z, ((K ⊗ₖ (1 : Mat z))*ρ*(K ⊗ₖ (1 : Mat z))ᴴ) (i,k) (j,k)) = _
  simp_rw [he]
  simp only [mul_apply,partialRight,conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_comm

theorem sourceBlock_sum {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) (n : ℕ) : run e t n = ∑ f, sourceBlock e t n f f := by
  rw [← purifiedVector_reduces]
  ext i j
  simp only [partialRight,sourceBlock,Matrix.sum_apply,Matrix.submatrix_apply]

def terminalAffineHomogenize {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (F : PrefixMatrices S →ᵃ[ℝ] ℝ) : terminalSpan S h →ₗ[ℝ] ℝ :=
  F.linear.comp (terminalPrefixReadout S h) + F 0 • terminalMass S h

theorem terminalAffineHomogenize_actual {I : Inventory} (S : Schedule I) (h : 0 < S.visits)
    (F : PrefixMatrices S →ᵃ[ℝ] ℝ) {r : ℕ} (t : Tester S r) :
    terminalAffineHomogenize S h F (terminalTesterVector S h t) = F (fun b => prefixGram b t) := by
  simp only [terminalAffineHomogenize,LinearMap.add_apply,LinearMap.comp_apply,
    terminalPrefixReadout_actual,LinearMap.smul_apply,terminalMass_tester,smul_eq_mul,mul_one]
  simpa only [vadd_eq_add,add_zero] using (F.map_vadd (0 : PrefixMatrices S) (fun b => prefixGram b t)).symm

#print axioms terminalCut
#print axioms terminalBodyKernel
#print axioms terminal_kernel_lift
#print axioms partialRight_rect_sandwich
#print axioms sourceBlock_sum
#print axioms terminalAffineHomogenize
#print axioms terminalAffineHomogenize_actual
end ScheduleLaw.Blueprint
