import FactoryRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FactoryFamilyAssembly
open History

theorem family {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef) (C : SmallResidueCoding τ) :
    FactoryFamily β τ q := by
  let Λ := FactoryRealization.spectralSize β q
  let A := FactoryCodingBounds.constant β d Λ
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hG := FactoryCodingBounds.gapConstant_nonneg β hβ d hd Λ hΛ
  have hA : 0 ≤ A := by dsimp [A,FactoryCodingBounds.constant]; positivity
  refine ⟨FactoryFamilyRates.debit β τ q C,FactoryFamilyRates.error C,A,hA,
    FactoryFamilyRates.debit_limit β τ q C,FactoryFamilyRates.error_vanishes C,
    FactoryFamilyRates.error_nonneg C,?_⟩
  have hr := FactoryFamilyRates.predecessor_tendsto.eventually (FactoryUniformBounds.residue_eventually C)
  filter_upwards [hr,eventually_ge_atTop 1] with m hmR hm
  intro η f hη hf
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  have hR : Real.log (C.residue n : ℝ) ≤ (n+1 : ℝ) := by simpa using hmR
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ,A,Λ] using
    FactoryRealization.realizes hd β hβ τ q hq C n hR η f hη hf

end ScheduleLaw.Blueprint.FactoryFamilyAssembly


