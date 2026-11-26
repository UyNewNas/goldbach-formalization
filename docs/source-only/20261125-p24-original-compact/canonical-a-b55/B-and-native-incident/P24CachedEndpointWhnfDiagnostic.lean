import ImbalancedChen.P2OriginalCompactCachedRun
import Lean

/-!
Uncompiled second diagnostic after the actual raw isDefEq result was false.
Run exactly one ordinary Meta.whnf on the unchanged original Bool target.
No isDefEq retry, proof assignment, evaluator snapshot, transparency change,
resource increase, or claim of original B / replay / owned-audit acceptance.
The closed term is unrestricted; the original external limits still apply.
-/

namespace P24CachedEndpointWhnfDiagnostic

open Lean Meta Elab Command

private def emit (value : Json) : MetaM Unit := do
  let stream ← IO.getStdout
  stream.putStrLn ("P24_B_WHNF " ++ value.compress)
  stream.flush

private def headRecord (original : Expr) : Json :=
  let value := original.consumeMData
  let head := value.getAppFn
  let kind := match head with
    | .const .. => "constant"
    | .fvar .. => "free_variable"
    | .mvar .. => "metavariable"
    | .bvar .. => "bound_variable"
    | .sort .. => "sort"
    | .lam .. => "lambda"
    | .forallE .. => "forall"
    | .letE .. => "let"
    | .lit .. => "literal"
    | .proj .. => "projection"
    | .mdata .. => "metadata"
    | .app .. => "application"
  let constant : Option String := match head with
    | .const name _ => some name.toString
    | _ => none
  Json.mkObj [("kind", toJson kind), ("constant", toJson constant),
    ("application_arguments", toJson value.getAppNumArgs)]

private def probe : MetaM Unit := do
  let options ← getOptions
  let defaultTransparency := (← getTransparency) == .default
  emit <| Json.mkObj [
    ("phase", toJson "begin"),
    ("maxRecDepth_option", toJson (maxRecDepth.get options)),
    ("maxHeartbeats_option", toJson (maxHeartbeats.get options)),
    ("effective_maxRecDepth", toJson (← MonadRecDepth.getMaxRecDepth)),
    ("default_transparency", toJson defaultTransparency),
    ("original_B_compile_credit", toJson false)]
  unless defaultTransparency do throwError "Unexpected inherited Meta transparency"
  tryCatchRuntimeEx
    (do
      let result ← whnf (mkConst
        `ImbalancedChen.P2OriginalCompactCachedRunSourceOnly.cachedHistoricalEndpointCheck)
      let result := result.consumeMData
      -- Emit structural facts before pretty-printing, so formatting failure
      -- cannot conceal the fact that whnf already returned.
      emit <| Json.mkObj [
        ("phase", toJson "whnf_returned"), ("head", headRecord result),
        ("is_Bool_true", toJson (result.isConstOf ``Bool.true)),
        ("is_Bool_false", toJson (result.isConstOf ``Bool.false)),
        ("direct_argument_heads", Json.arr (result.getAppArgs.map headRecord)),
        ("original_B_compile_credit", toJson false)]
      let pretty := (← ppExpr result).pretty
      emit <| Json.mkObj [
        ("phase", toJson "complete"), ("pretty_default_options", toJson pretty),
        ("pretty_contains_ellipsis", toJson (pretty.contains '⋯')),
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
        ("message", toJson (← exception.toMessageData.toString)),
        ("original_B_compile_credit", toJson false),
        ("kernel_replay_credit", toJson false), ("owned_audit_credit", toJson false)]
      throw exception)

set_option maxRecDepth 0 in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM probe

end P24CachedEndpointWhnfDiagnostic
