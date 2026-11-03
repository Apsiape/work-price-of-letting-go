import Recorder
import CircuitBounds
import FlatStock
import IdleExtension

/-! Rare, input-independent recorder branch and its uniform operational bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace Recorder

/-- All record stock and the source flag are in the new finite retained body.
The ordinary branch carries flat stock; the recorder branch carries fresh EPR
stock and an idle copy of the original source. The flag sectors are represented
as the direct sum of their fully counted body spaces. -/
def rare {I : Inventory} {S : Schedule I} (e : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : Extension S :=
  ClassicalFlag.extension (IdleExtension.extension e (flatStock S))
    (IdleExtension.extension (extension S) e) δ hδ hδ1

theorem rare_service {I : Inventory} {S : Schedule I} (e : Extension S)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : Approximates (rare e δ hδ hδ1) e δ := by
  have he := ClassicalFlag.approximates_left (IdleExtension.extension e (flatStock S))
    (IdleExtension.extension (extension S) e) δ hδ hδ1
  intro r t
  simpa only [IdleExtension.observerOutput_idle] using he r t

def perturbationConstant {I : Inventory} {S : Schedule I} (β : ℝ)
    (_e : Extension S) (g : ℝ) : ℝ := max 0 (scoreBound β (extension S) - g)

theorem perturbationConstant_nonneg {I : Inventory} {S : Schedule I} (β : ℝ)
    (e : Extension S) (g : ℝ) : 0 ≤ perturbationConstant β e g := le_max_left _ _

/-- A fixed finite block constant controls the score change uniformly over all
tester memory dimensions and all adaptive tester gates. -/
theorem rare_score {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g : ℝ) (he : ∀ r (t : Tester S r), score β e t ≤ g)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ) (t : Tester S r) :
    score β (rare e δ hδ hδ1) t ≤ g + δ * perturbationConstant β e g := by
  have he' : ∀ r (t : Tester S r), score β (IdleExtension.extension e (flatStock S)) t ≤ g := by
    intro r t
    rw [IdleExtension.score_idle]
    exact he r t
  have hf' : ∀ r (t : Tester S r), score β (IdleExtension.extension (extension S) e) t ≤
      scoreBound β (extension S) := by
    intro r t
    rw [IdleExtension.score_idle]
    exact score_le_bound β hβ (extension S) r t
  have hs := ClassicalFlag.score_bound β (IdleExtension.extension e (flatStock S))
    (IdleExtension.extension (extension S) e) δ hδ hδ1 g
    (scoreBound β (extension S)) he' hf' r t
  have hm : δ * (scoreBound β (extension S) - g) ≤ δ * perturbationConstant β e g :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hδ
  exact hs.trans (by linarith)

/-- The rare recorder can be chosen with strictly positive probability while
both its complete service error and its score increment meet any tolerance. -/
theorem small_rare_branch {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g : ℝ) (he : ∀ r (t : Tester S r), score β e t ≤ g)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδ1 : δ ≤ 1,
      Approximates (rare e δ hδ.le hδ1) e ν ∧
      (∀ r (t : Tester S r), score β (rare e δ hδ.le hδ1) t ≤ g+ν) ∧
      δ * perturbationConstant β e g ≤ ν := by
  let C := perturbationConstant β e g
  have hC : 0 ≤ C := perturbationConstant_nonneg β e g
  have hCp : 0 < C+1 := by linarith
  let δ := min (1/2 : ℝ) (ν/(C+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hν hCp)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδCp : δ * (C+1) ≤ ν := (le_div_iff₀ hCp).mp (min_le_right _ _)
  have hδν : δ ≤ ν := by nlinarith
  have hδC : δ*C ≤ ν := by nlinarith
  refine ⟨δ,hδ,hδ1,approximates_mono (rare_service e δ hδ.le hδ1) hδν,?_,hδC⟩
  intro r t
  exact (rare_score β hβ e g he δ hδ.le hδ1 r t).trans (by linarith)

end Recorder
end ScheduleLaw
