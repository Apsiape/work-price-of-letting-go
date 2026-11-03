import CombRealization

/-! An explicit lawful coherent tester, and the unconditional zero-visit
case of converse realization. No realization hypothesis is used here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

def idleTester {I : Inventory} (S : Schedule I) : Tester S 1 where
  initial x := if x = ((0 : Fin 1),fun c => ⟨0,I.dim_pos c⟩) then 1 else 0
  normalized := by
    simp only [apply_ite,Complex.normSq_one,Complex.normSq_zero]
    simp
  gate _ := 1
  unitary _ := by constructor <;> simp
  gate_local k := by
    simpa only [permMatrix_refl] using Recorder.local_permutation I 1 (held S k)ᶜ
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)

theorem zero_visit_comb_realization {I : Inventory} (S : Schedule I) (h : S.visits = 0)
    (Z : PrefixMatrices S) :
    ∃ (r : ℕ) (t : Tester S r), ∀ b, prefixGram b t = Z b := by
  refine ⟨1,idleTester S,?_⟩
  intro b
  have he := b.val.val.isLt
  omega

theorem actualTesterFamilies_nonempty {I : Inventory} (S : Schedule I) :
    (actualTesterFamilies S).Nonempty :=
  ⟨(fun b => prefixGram b (idleTester S)),1,idleTester S,fun _ => rfl⟩

end ScheduleLaw.History
