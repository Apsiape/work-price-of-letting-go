import BlueprintFinitePrimitives
import BoundedSourceCoding
import FactoryFamilyAssembly

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint

/-- Physical four-register factory from bounded-residue coding. The conclusion
retains the complete original Formation and FactoryFamily contracts: actual Gibbs
batch, all retired stocks, tunable controller return, entropy, absolute battery
tail, defect for all references, and charged startup capital. -/
theorem finite_factory_of_small_residue_coding {d : ℕ} (hd : 0 < d)
    (β : ℝ) (hβ : 0 < β) (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (C : SmallResidueCoding τ) : FactoryFamily β τ q := by
  exact FactoryFamilyAssembly.family hd β hβ τ q hq C

end ScheduleLaw.Blueprint
