import Lake
open Lake DSL
package scheduleLaw where
  moreLeanArgs := #["-j1", "-M6144"]
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"
lean_lib QuantumInfo where
  srcDir := "vendor/PhyslibQuantumInfo"
  roots := #[`QuantumInfo.Entropy.SSA, `QuantumInfo.Entropy.Relative, `QuantumInfo.Entropy.DPI]
@[default_target]
lean_lib ScheduleLaw where
  srcDir := "src"
  roots := #[`Round28Audit]
