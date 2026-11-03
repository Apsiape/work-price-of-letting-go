import BlueprintEngine
import BlueprintAttainment
import BlueprintJointTangent

/-! The round-9 blueprint root. Its three assemblies have the exact Challenge
conclusions and do not import Challenge. Admissions are isolated in the named
blueprint groups and exposed by BlueprintAudit, pending the zero-admission gate. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace ScheduleLaw.Blueprint

theorem corrected_joint_tangent :
    ∀ β : ℝ, 0 < β → ∀ (I : Inventory) (S : Schedule I) (e : Extension S) (g : ℝ),
      (∀ r (t : Tester S r), score β e t ≤ g) →
      ∀ s : ℝ, 0 < s → s < 1 →
      ∃ q : Density (Fin e.b), q.matrix.PosDef ∧
        ∃ w : ℝ,
          (∀ r (t : Tester S r),
            handoff e t + energy (((-1 / β : ℝ) : ℂ) • matrixLog q.matrix)
              (bodyOutput e t - e.source.matrix) ≤ w) ∧
          (∃ (r : ℕ) (t : Tester S r),
            handoff e t + energy (((-1 / β : ℝ) : ℂ) • matrixLog q.matrix)
              (bodyOutput e t - e.source.matrix) = w) ∧
          faithfulRelativeEntropy e.source.matrix q.matrix / β + w ≤
            g - Real.log (1-s) / β := by
  intro β hβ I S e g hg s hs hs1
  exact joint_tangent β hβ e g hg s hs hs1

theorem pointwise_physical_compiler :
    ∀ β : ℝ, 0 < β → ∀ (I : Inventory) (S : Schedule I) (e : Extension S) (g : ℝ),
      (∀ r (t : Tester S r), score β e t ≤ g) →
      ∀ ν : ℝ, 0 < ν → ∃ (d : Engine S β) (b : Budget),
        Approximates d.extension e ν ∧ MeetsBudget d b ∧
        b.productError ≤ ν ∧ b.controllerEnergy ≤ ν ∧ b.controllerEntropy ≤ ν ∧
        b.batteryEntropy ≤ ν ∧ b.failureProbability ≤ ν ∧ b.absoluteTail ≤ ν ∧
        nominalDebit d ≤ g + ν := by
  intro β hβ I S e g hg ν hν
  obtain ⟨d,b,hs,hb,⟨h1,h2,h3,h4,h5,h6⟩,hd⟩ := compile_pointwise β hβ e g hg ν hν
  exact ⟨d,b,hs,hb,h1,h2,h3,h4,h5,h6,hd⟩

theorem work_law_for_schedules :
    ∀ β : ℝ, 0 < β → ∀ T : TaskFamily, WorkLaw β T ∧ WorkLawBits β T := by
  intro β hβ T
  have ha := optimal_equality_attainment β hβ T
  have law : WorkLaw β T := ⟨(fun d => regularized_converse_from_circuit hβ T d),ha.1,ha.2⟩
  exact ⟨law,workLaw_implies_bits β hβ T law⟩


end ScheduleLaw.Blueprint
