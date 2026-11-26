import ImbalancedChen.P2OriginalCompactQ80CacheEncloser
import ImbalancedChen.P2OriginalCompactConcreteLoop
import Lean.Elab.Tactic.Decide

/-!
Independent final-interface draft; no production or tested source is changed.
The four formula declarations below are copied verbatim from prefix-03.
The two new mathematical lemmas transport one proved sourceTable node into
the original cached total. They retain firstBounds, the original log/tail
operation order, historicalUpper and Q80 scaling.

finishFromSourceNode is not invoked in this draft. Its only evaluation
request is a separate arithmetic proposition obtained from the checked
generic bridge; it never asks a reducer to evaluate the original table.
No literal node value, table data or new endpoint number is installed.
The original public statements and their resource options remain untouched.

The planned integration keeps the original public theorem as caller and keeps
both resource-option lines at their original locations and with their original
scope. The caller wraps the complete generator and this finisher together in
one official auxiliary-naming scope: get the current declaration-name prefix;
if it is public, use withDeclNameForAuxNaming on mkPrivateName of that SAME
current prefix. Do not rebase naming to another existing helper. The independent
public-entry diagnostic must validate this plan before production integration.

No separate private worker or extra option scope is introduced. Retain the
original archivedOriginalUpper definition and both public headers byte-for-byte;
retain the second public theorem's proof. This draft invokes no finite proof.
-/

namespace P24Q80ArchivedTotalInterface

open ImbalancedChen
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80CacheEncloserSourceOnly

private def d10OfReader (read : Nat → Node) : ℤ :=
  up ((read (10 * 16384)).hh - (read (10 * 16384)).ll) (10 : ℤ)

private def tailIntervalOfD10 (d : ℤ) : I80 :=
  let d0 := I80.raw d
  let ell := logI (rho/cutoff)
  let poly := (ell.mul ell).add ((I80.point 2).mul ell) |>.add (I80.point 2)
  historicalDiv
    (((((I80.point 2).mul d0).mul (I80.point (10^2))).mul
      (I80.point cutoff)).mul poly)
    (I80.point ((rho-cutoff)^2))

private def fixedUpperOfD10 (d : ℤ) : ℚ :=
  4/theta + ((firstBounds.upper+(tailIntervalOfD10 d).hi : ℤ) : ℚ)/(scale : ℚ)

private theorem fixedUpperWith_factor :
    fixedUpperWith =
      fun nodes => fixedUpperOfD10 (d10OfReader (lookup nodes)) := by
  funext nodes
  rfl

/-- A single source-node certificate suffices for the complete fixed term.
All array/source-table transport is symbolic. -/
private theorem fixedUpper_from_source_node (value : Node)
    (hnode : sourceTable (10 * 16384) = value) :
    fastFixedUpper =
      fixedUpperOfD10 (up (value.hh - value.ll) (10 : ℤ)) :=
  (congrFun fixedUpperWith_factor tableArray).trans
    (congrArg fixedUpperOfD10
      (congrArg (fun node : Node => up (node.hh - node.ll) (10 : ℤ))
        ((congrFun tableArray_lookup (10 * 16384)).trans hnode)))

/-- The final proof input is the small original arithmetic expression.
In production, target is the unchanged archivedOriginalUpper expression. -/
private theorem cached_total_from_source_node (value : Node) (target : ℚ)
    (hnode : sourceTable (10 * 16384) = value)
    (harithmetic :
      fixedUpperOfD10 (up (value.hh - value.ll) (10 : ℤ)) +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
          target) :
    fastFixedUpper +
      (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
        target :=
  (congrArg
    (fun q : ℚ =>
      q + (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ))
    (fixedUpper_from_source_node value hnode)).trans harithmetic

open Lean Meta Elab Tactic

/-- Assembly draft for a caller that already produced a checked, closed source
node certificate. The raw +kernel core preserves the original exception.
The generated arithmetic declaration is a theorem, never a value definition.
All generated declarations still require the original complete owned audit. -/
private def finishFromSourceNode (value hnode : Expr) : TacticM Unit := withMainContext do
  unless !value.hasFVar && !value.hasMVar && !hnode.hasFVar && !hnode.hasMVar do
    throwError "The final node value and source certificate must be closed"
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, _, archived) := target.eq?
    | throwError "The original rational equality goal is required"
  let bridge ← mkAppM ``cached_total_from_source_node #[value, archived, hnode]
  let bridgeType ← inferType bridge
  let .forallE _ smallGoal _ _ := bridgeType
    | throwError "The source-node bridge did not expose its arithmetic premise"
  unless !smallGoal.hasFVar && !smallGoal.hasMVar do
    throwError "The final arithmetic proposition must be closed"
  let proof ← mkDecideProof smallGoal
  let smallName ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] smallGoal proof (kind? := some `_p24FinalArithmetic)
  let info ← getConstInfo smallName
  unless isPrivateName smallName do
    throwError "The generated arithmetic theorem must be private"
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "The arithmetic certificate is not a theorem declaration"
  if info.isUnsafe || info.isPartial || info.isAxiom then
    throwError "The arithmetic certificate failed the declaration boundary"
  let finalProof := mkApp bridge (mkConst smallName)
  unless (← isDefEq (← inferType finalProof) target) do
    throwError "The assembled theorem does not match the unchanged public goal"
  goal.assign finalProof
  replaceMainGoal []

#print axioms fixedUpperWith_factor
#print axioms fixedUpper_from_source_node
#print axioms cached_total_from_source_node

end P24Q80ArchivedTotalInterface

