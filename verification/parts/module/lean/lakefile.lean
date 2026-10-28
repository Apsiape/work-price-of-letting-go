import Lake
open Lake DSL

package proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib Proofs where
  roots := #[`Gibbs, `Order, `HiddenBit, `Lift, `Converse, `Counting, `Repair, `Binning, `Ladder, `Factory]
