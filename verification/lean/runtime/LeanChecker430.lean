/-
Lean 4.30 NDJSON kernel replay driver. The NDJSON parser is ported from the
Lean FRO exporter sources, with provenance recorded alongside this file.
This runtime is never imported by the certified proof modules.
-/
import Lean.CoreM
import Lean.Replay
import LeanExport.Parse
open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal

def permitted : List Name := [``propext,``Classical.choice,``Quot.sound]
def required : List Name := [`ScheduleLaw.Blueprint.pointwise_physical_compiler,
  `ScheduleLaw.Blueprint.work_law_for_schedules,
  `ScheduleLaw.Blueprint.corrected_joint_tangent]

def main (args : List String) : IO UInt32 := do
  let [exportFile] := args | throw <| IO.userError "Exactly one NDJSON file is required"
  initSearchPath (← findSysroot)
  let standard ← importModules #[{ module := `Init }] {}
  IO.FS.withFile exportFile .read fun handle => do
    let exported ← LeanExport.parseStream (.ofHandle handle)
    for n in required do
      unless exported.constMap.contains n do
        throw <| IO.userError s!"Missing required original root: {n}"
    for (n,ci) in exported.constMap.toList do
      if ci.isAxiom && permitted.contains n then
        let some original := standard.find? n |
          throw <| IO.userError s!"Permitted axiom absent from pinned Init: {n}"
        unless ci.toConstantVal == original.toConstantVal do
          throw <| IO.userError s!"Permitted axiom signature differs from pinned Init: {n}"
      if ci.isAxiom && !permitted.contains n then
        throw <| IO.userError s!"Unpermitted axiom: {n}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"Unsafe/partial constant in proof export: {n}"
    let quotTargets := [`Quot.mk,`Quot.lift,`Quot.ind]
    let constants := quotTargets.foldl (init := exported.constMap) (·.erase ·)
    let checked ← (← mkEmptyEnvironment).replay constants
    for n in required do
      unless (checked.toKernelEnv.find? n).isSome do
        throw <| IO.userError s!"Required root absent after kernel replay: {n}"
    for n in (`Quot :: quotTargets) do
      if let some original := exported.constMap[n]? then
        let some regenerated := checked.toKernelEnv.find? n |
          throw <| IO.userError s!"Missing regenerated quotient constant: {n}"
        unless (match original,regenerated with
          | .quotInfo a,.quotInfo b => a==b
          | _,_ => false) do
          throw <| IO.userError s!"Quotient constant mismatch: {n}"
    IO.println s!"Lean {Lean.versionString} kernel accepted the identical closed export ({exported.constMap.size} constants)"
    pure 0
