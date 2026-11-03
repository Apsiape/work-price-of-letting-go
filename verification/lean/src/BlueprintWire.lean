import BlueprintComb
import BlueprintWireReadout
import BlueprintStockRecovery
import BlueprintKernelBase
import BlueprintKernelInduction
import BlueprintStockPast
import BlueprintEndpointEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

/-- The kernels are chosen before both the memory dimension and the tester. -/
theorem schedule_kernel_induction {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∃ K : (k : Cut S) → Fin e.f → CutKernel e k,
      ∀ (r : ℕ) (t : Tester S r) (k : Cut S) (f g : Fin e.f),
        sourceBlock e t (k.val+1) f g =
          kernelLift e k r (K k f) * rawState t (k.val+1) *
            (kernelLift e k r (K k g))ᴴ := by
  exact schedule_kernel_from_routed e

/-- Final empty-owned-space contraction, including zero visits. -/
theorem body_stock_readout {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∃ B : Mat (Recorder.Stock S) →ₗ[ℝ] Mat (Fin e.b),
      ∀ (r : ℕ) (t : Tester S r), B (terminalStock t) = bodyOutput e t := by
  obtain ⟨K,hK⟩ := schedule_kernel_induction e
  let B : Mat (Recorder.Stock S) →ₗ[ℝ] Mat (Fin e.b) :=
    ∑ f, (sandwichLinear (terminalBodyKernel e (K (terminalCut S) f))).restrictScalars ℝ
  refine ⟨B,?_⟩
  intro r t
  have hr := sourceBlock_sum e t (2*S.visits+1)
  have hbf (f : Fin e.f) : sourceBlock e t (2*S.visits+1) f f =
      ((terminalBodyKernel e (K (terminalCut S) f)) ⊗ₖ (1 : Mat (Payload I × Fin r)))*
        rawState t (2*S.visits+1)*
          ((terminalBodyKernel e (K (terminalCut S) f)) ⊗ₖ (1 : Mat (Payload I × Fin r)))ᴴ := by
    have ht := hK r t (terminalCut S) f f
    rw [terminal_kernel_lift e (K (terminalCut S) f) r] at ht
    exact ht
  unfold bodyOutput finalState
  rw [hr]
  ext i j
  simp only [B,LinearMap.sum_apply,LinearMap.restrictScalars_apply,sandwichLinear,
    LinearMap.coe_mk,AddHom.coe_mk,terminalStock,partialRight,Matrix.sum_apply,Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  have he := partialRight_rect_sandwich (terminalBodyKernel e (K (terminalCut S) f))
    (rawState t (2*S.visits+1))
  rw [hbf]
  exact congrFun₂ he.symm i j

/-- Tagged arrival/release carrier energy carried to the retained stock.
No kernel may depend on the tester; all source-purifier blocks are retained. -/
theorem endpoint_energy_stock_readout {I : Inventory} {S : Schedule I} (e : Extension S)
    (v : Fin S.visits) (o : Bool) :
    ∃ L : Mat (Recorder.Stock S) →ₗ[ℝ] ℝ, ∀ (r : ℕ) (t : Tester S r),
      L (terminalStock t) = carrierEnergy e (run e t ((S.position (v,o)).val+1)) (S.carrier v) := by
  exact endpoint_energy_from_routed e v o

theorem handoff_stock_readout {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∃ E : Mat (Recorder.Stock S) →ₗ[ℝ] ℝ,
      ∀ (r : ℕ) (t : Tester S r), E (terminalStock t) = handoff e t := by
  classical
  choose L hL using endpoint_energy_stock_readout e
  refine ⟨∑ v, (L v true-L v false),?_⟩
  intro r t
  simp only [LinearMap.sum_apply,LinearMap.sub_apply,hL,handoff]

/-- The original prefixes determine the entire final stock marginal;
unused partner factors are explicitly included in this affine map. -/
theorem terminal_stock_affine {I : Inventory} (S : Schedule I) :
    ∃ R : PrefixMatrices S →ᵃ[ℝ] Mat (Recorder.Stock S),
      ∀ (r : ℕ) (t : Tester S r), R (fun b => prefixGram b t) = terminalStock t := by
  by_cases hz : S.visits=0
  · refine ⟨AffineMap.const ℝ (PrefixMatrices S)
      ((zeroVisitBody (Recorder.extension S)).submatrix (Recorder.stockFin S) (Recorder.stockFin S)),?_⟩
    intro r t
    change _ = partialRight (rawState t (2*S.visits+1))
    rw [rawStock_body]
    change _ = (bodyOutput (Recorder.extension S) t).submatrix (Recorder.stockFin S) (Recorder.stockFin S)
    rw [bodyOutput_zero_visits _ hz]
    rfl
  · let h : 0 < S.visits := Nat.pos_of_ne_zero hz
    exact ⟨(terminalStockLinear S h).toAffineMap,fun r t => terminalStockLinear_actual S h t⟩

theorem operational_affine_maps {I : Inventory} {S : Schedule I} (e : Extension S) :
    ∃ (B : PrefixMatrices S →ᵃ[ℝ] Mat (Fin e.b)) (E : PrefixMatrices S →ᵃ[ℝ] ℝ),
      ∀ (r : ℕ) (t : Tester S r),
        B (fun b => prefixGram b t) = bodyOutput e t ∧
        E (fun b => prefixGram b t) = handoff e t := by
  obtain ⟨B,hB⟩ := body_stock_readout e
  obtain ⟨E,hE⟩ := handoff_stock_readout e
  obtain ⟨R,hR⟩ := terminal_stock_affine S
  exact ⟨B.toAffineMap.comp R,E.toAffineMap.comp R,fun r t => by
    change B (R _) = _ ∧ E (R _) = _
    rw [hR]; exact ⟨hB r t,hE r t⟩⟩

/-- Uses eliminate_comb only through actualTesterFamilies_eq_causal. -/
theorem operational_image_geometry {I : Inventory} {S : Schedule I} (e : Extension S) :
    IsCompact (OperationalImage e) ∧ Convex ℝ (OperationalImage e) ∧
      (OperationalImage e).Nonempty ∧ SectionDensities e.b (OperationalImage e) := by
  obtain ⟨B,E,hBE⟩ := operational_affine_maps e
  let F := B.prod E
  have heq : OperationalImage e=F '' {Z : PrefixMatrices S | IsCausalPrefixFamily S Z} := by
    ext x
    constructor
    · rintro ⟨r,t,rfl⟩
      refine ⟨(fun b => prefixGram b t),actual_causal_prefix_family S t,?_⟩
      exact Prod.ext (hBE r t).1 (hBE r t).2
    · rintro ⟨Z,hZ,rfl⟩
      obtain ⟨r,t,ht⟩ := realize_causal_prefix_family eliminate_comb S Z hZ
      refine ⟨r,t,?_⟩
      have ht' : (fun b => prefixGram b t)=Z := funext ht
      have hb := hBE r t
      rw [ht'] at hb
      exact Prod.ext hb.1 hb.2
  refine ⟨?_,?_,?_,?_⟩
  · rw [heq]
    exact (isCompact_causal_prefix_set S).image F.continuous_of_finiteDimensional
  · rw [heq]
    exact (causal_prefix_convex S).affine_image F
  · exact ⟨(bodyOutput e (idleTester S),handoff e (idleTester S)),1,idleTester S,rfl⟩
  · rintro x ⟨r,t,rfl⟩
    exact bodyOutput_density e t

theorem physical_J_terminal {I : Inventory} {S : Schedule I} (β : ℝ)
    (e : Extension S) (q : Density (Fin e.b)) (h : 0 < S.visits) :
    ∃ J : terminalSpan S h →ₗ[ℝ] ℝ,
      ∀ (r : ℕ) (t : Tester S r), J (terminalTesterVector S h t) = physicalLinearized β e q t := by
  obtain ⟨B,E,hBE⟩ := operational_affine_maps e
  let H := tangentHamiltonian β q
  let F : PrefixMatrices S →ᵃ[ℝ] ℝ := E+(energyLinear H).toAffineMap.comp B-
    AffineMap.const ℝ (PrefixMatrices S) (energy H e.source.matrix)
  refine ⟨terminalAffineHomogenize S h F,?_⟩
  intro r t
  rw [terminalAffineHomogenize_actual]
  change E _+energy H (B _)-energy H e.source.matrix=physicalLinearized β e q t
  rw [(hBE r t).1,(hBE r t).2]
  unfold physicalLinearized
  have he : energy H (bodyOutput e t-e.source.matrix)=
      energy H (bodyOutput e t)-energy H e.source.matrix := (energyLinear H).map_sub _ _
  rw [he]
  ring

end ScheduleLaw.Blueprint
