import BlueprintCache
import BlueprintPhase

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

theorem traceDistance_triangle {a : Type} [Fintype a] [DecidableEq a]
    (A B C : Mat a) : traceDistance A C ≤ traceDistance A B + traceDistance B C := by
  unfold traceDistance
  simp only [ClassicalFlag.traceNorm_eq_library]
  have he : A-C = (A-B)+(B-C) := by abel
  have h := Matrix.traceNorm_add_le (A-B) (B-C)
  rw [← he] at h
  linarith

theorem approximates_triangle {I : Inventory} {S : Schedule I} (a b c : Extension S)
    (ε η : ℝ) (ha : Approximates a b ε) (hb : Approximates b c η) :
    Approximates a c (ε+η) := by
  intro r t
  exact (traceDistance_triangle (observerOutput a t) (observerOutput b t)
    (observerOutput c t)).trans (add_le_add (ha r t) (hb r t))

theorem compile_pointwise {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g : ℝ) (hg : ∀ r (t : Tester S r), score β e t ≤ g)
    (ν : ℝ) (hν : 0 < ν) : CompilerConclusion β e g ν := by
  have hη : 0 < ν/16 := by positivity
  obtain ⟨P⟩ := initialized_heat_plan β hβ e g hg (ν/16) hη
  have hf := source_factory_circuits P.bare.b_pos β hβ P.bare.source P.reference P.faithful
  obtain ⟨p,b,hc,hservice,hbudget,hsmall,hdef,hdebit⟩ := cyclic_cache_protocol β hβ e g (ν/16) hη P hf
  have hd : ∀ r (t : Tester S r), |Driven.defect p t| ≤ 2*(ν/16) :=
    fun r t => (hdef r t).trans (by have := P.residual_small; linarith)
  obtain ⟨d,B,hds,hdb,hbs,hdd,hcapital⟩ := finite_conserving_phase β hβ p b (ν/16) (ν/4)
    hη (by positivity) hbudget hsmall hc hd
  refine ⟨d,B,?_,hdb,?_,?_⟩
  · exact approximates_mono (approximates_triangle d.extension P.bare e _ _
      (approximates_triangle d.extension p.extension P.bare _ _ hds hservice) P.service) (by linarith)
  · rcases hbs with ⟨h1,h2,h3,h4,h5,h6⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · have := P.rate; linarith

end ScheduleLaw.Blueprint
