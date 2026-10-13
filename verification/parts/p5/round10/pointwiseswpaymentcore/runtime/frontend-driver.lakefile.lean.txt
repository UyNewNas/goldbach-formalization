import Lake
import Lean.Elab.Frontend

open Lake DSL

package p1FrontendDriver

/-- Invoke the unchanged Lean frontend API at trust level zero. -/
def compileOneBody (args : List String) : IO UInt32 := do
  let [sourceName, moduleName, outputName, strictName] := args
    | throw <| IO.userError "usage: compileOne SOURCE MODULE OUTPUT strict|normal"
  unless strictName == "strict" || strictName == "normal" do
    throw <| IO.userError "invalid diagnostics mode"
  let some root ← IO.getEnv "LEAN_SYSROOT"
    | throw <| IO.userError "LEAN_SYSROOT must be explicitly set"
  Lean.initSearchPath root
  unsafe Lean.enableInitializersExecution
  let source := System.FilePath.mk sourceName
  let output := System.FilePath.mk outputName
  if let some parent := output.parent then
    IO.FS.createDirAll parent
  let input ← IO.FS.readFile source
  let opts := Lean.Options.empty.setBool `warningAsError (strictName == "strict")
  IO.println s!"FRONTEND_START module={moduleName} trustLevel=0 strict={strictName} Lean.githash={Lean.githash}"
  let result ← Lean.Elab.runFrontend input opts sourceName moduleName.toName
    (trustLevel := 0) (oleanFileName? := some output)
  match result with
  | none =>
    IO.eprintln s!"FRONTEND_FAILED module={moduleName}"
    return 1
  | some _ =>
    IO.println s!"FRONTEND_OK module={moduleName} trustLevel=0"
    return 0

/-- Scheduling only: wait for the two pre-existing frontends to exit, then serialize new frontends. -/
script compileOne (args) do
  let ready := System.FilePath.mk "/workspace/scratch/127408f63891/lean-runtime/logs/resource-adjustment-01/legacy-drained.ok"
  let failed := System.FilePath.mk "/workspace/scratch/127408f63891/lean-runtime/logs/resource-adjustment-01/legacy-drain.failed"
  let lockFile := System.FilePath.mk "/workspace/scratch/127408f63891/lean-runtime/logs/resource-adjustment-01/frontend.lock"
  IO.println s!"P1_SCHEDULER_WAIT_DRAIN module={args.getD 1 ""}"
  (← IO.getStdout).flush
  while !(← ready.pathExists) do
    if ← failed.pathExists then
      throw <| IO.userError "The pre-existing frontend drain failed; no new frontend started"
    IO.sleep 500
  return ← IO.FS.withFile lockFile .append fun handle => do
    handle.lock
    try
      IO.println s!"P1_SCHEDULER_SERIAL_BEGIN module={args.getD 1 ""}"
      (← IO.getStdout).flush
      compileOneBody args
    finally
      handle.unlock
