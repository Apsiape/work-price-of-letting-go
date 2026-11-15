import Lake
open Lake DSL

package proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib Proofs where
  roots := #[`Gibbs, `Order, `HiddenBit, `Lift, `Converse, `Counting, `Repair, `Binning, `Ladder, `Factory]
