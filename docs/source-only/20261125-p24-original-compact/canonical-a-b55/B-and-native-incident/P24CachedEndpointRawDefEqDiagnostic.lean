import ImbalancedChen.P2OriginalCompactCachedRun
import Lean

/-!
First, uncompiled diagnostic for the actual b55 B `rfl` failure.

This reproduces only applyRfl's Meta definitional-equality precheck, with its
approxDefEq configuration and the original two local zero options. It calls
isDefEq directly once so that an exception cannot silently become false through
isDefEqGuarded. It neither assigns nor checks an endpoint proof and supplies no
replacement table, state, evaluator, result, resource limit, or numerical input.

The original target remains closed and unrestricted: this probe is not a claim
that its execution time is bounded by the previous 4.312-second failure. The
unchanged external job limits remain the execution bound. A true result here
would still confer no original B compile, kernel replay, or owned-audit credit.
-/

namespace P24CachedEndpointRawDefEqDiagnostic

open Lean Meta Elab Command

private def emit (value : Json) : MetaM Unit := do
  let stream ← IO.getStdout
  stream.putStrLn ("P24_B_RAW_DEFEQ " ++ value.compress)
  stream.flush

private def rawProbe : MetaM Unit := do
  let options ← getOptions
  let begin := Json.mkObj [
    ("phase", toJson "begin"),
    ("maxRecDepth_option", toJson (maxRecDepth.get options)),
    ("maxHeartbeats_option", toJson (maxHeartbeats.get options)),
    ("effective_maxRecDepth", toJson (← MonadRecDepth.getMaxRecDepth)),
    ("current_recDepth", toJson (← MonadRecDepth.getRecDepth)),
    ("guarded_call_used", toJson false),
    ("original_B_compile_credit", toJson false)]
  emit begin
  let lhs := mkConst
    `ImbalancedChen.P2OriginalCompactCachedRunSourceOnly.cachedHistoricalEndpointCheck
  let rhs := mkConst ``Bool.true
  tryCatchRuntimeEx
    (do
      let result ← approxDefEq <| isDefEq lhs rhs
      emit <| Json.mkObj [
        ("phase", toJson "returned"), ("isDefEq", toJson result),
        ("original_B_compile_credit", toJson false),
        ("kernel_replay_credit", toJson false), ("owned_audit_credit", toJson false)])
    (fun exception => do
      let kind := match exception with
        | .error _ _ => "error"
        | .internal _ _ => "internal"
      emit <| Json.mkObj [
        ("phase", toJson "exception"), ("kind", toJson kind),
        ("isMaxRecDepth", toJson exception.isMaxRecDepth),
        ("isMaxHeartbeat", toJson exception.isMaxHeartbeat),
        ("isInterrupt", toJson exception.isInterrupt),
        ("message", toJson (← exception.toMessageData.toString)),
        ("original_B_compile_credit", toJson false),
        ("kernel_replay_credit", toJson false), ("owned_audit_credit", toJson false)]
      throw exception)

-- Exactly the two original B declaration-local option values; no increase.
set_option maxRecDepth 0 in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM rawProbe

end P24CachedEndpointRawDefEqDiagnostic
