import Lake
open Lake DSL

package proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib Proofs where
  roots := #[`Hadamard, `FiniteDevice, `WernerHolevo, `Qutrit, `FullReset, `Constants]
