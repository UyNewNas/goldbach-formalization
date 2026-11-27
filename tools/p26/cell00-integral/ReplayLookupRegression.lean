import Lean.CoreM
import Lean.Replay

/-! Regression for the inventory lookup after official Environment.replay.
The returned wrapper stores newly checked declarations in the kernel map. -/
open Lean

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Lean.CoreM }] {} 0
  let name := `p26Cell00ReplayLookupRegression
  let ci := ConstantInfo.defnInfo {
    name, levelParams := [], type := mkConst `Nat, value := mkNatLit 1,
    hints := .abbrev, safety := .safe }
  let additions := ({} : Std.HashMap Name ConstantInfo).insert name ci
  let checked ← env.replay additions
  unless (checked.find? name).isNone do
    throw <| IO.userError "Expected the old elaboration lookup to miss the new kernel entry"
  let some actual := checked.toKernelEnv.find? name
    | throw <| IO.userError "The corrected kernel lookup failed"
  let .defnInfo actual := actual
    | throw <| IO.userError "Replayed entry is not the submitted definition"
  unless actual.name == name && actual.type == mkConst `Nat &&
      actual.value == mkNatLit 1 && actual.safety == .safe do
    throw <| IO.userError "Replayed kernel entry differs"
  IO.println "P26_REPLAY_LOOKUP_REGRESSION_PASS"
  return 0
