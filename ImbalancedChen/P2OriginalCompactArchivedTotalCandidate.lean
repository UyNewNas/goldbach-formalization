import ImbalancedChen.P2OriginalCompactQ80CacheEncloser
import ImbalancedChen.P2OriginalCompactConcreteLoop
import Lean
import Lean.Meta.Tactic.Cbv
import Lean.Meta.Sym.LitValues
import Lean.Elab.Tactic.Decide

/-!
Source-only node-block candidate for the original archived whole upper equality.

The imported original Q80 nodeUpdate/sourceState definitions remain the source.
Private three-predecessor lemmas transport each fresh arithmetic proof to its
completed source node. An exact constant-prefix theorem supplies indices through
2*g; 2048 checked 64-node blocks compute indices 32769 through 163840. Only the
last completed node is transported to the full original 12*g source table.

The fixed-term bridge preserves the original first-series, logarithm, tail and
rational expressions. A separate small closed arithmetic theorem completes the
unchanged archived equality. No computed node, table, first or tail output is
installed as an evaluator definition. This module performs no adaptive run.

The standalone first-128 diagnostic passed compilation; its complete owned audit
and replay, adaptation under the original imports, full-prefix computation and
the original finite-A acceptance gates remain separate validation obligations.
This file is an uncompiled candidate and carries no canonical acceptance credit.
-/
namespace ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly

open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80CacheEncloserSourceOnly

namespace NodeStepProof

open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80CacheEncloserSourceOnly

/-- The exact original update arithmetic with its three reader arguments made
explicit. No computed node values are stored in this definition. -/
private def nodeFromThree (g i : ℕ) (p l r : Node) : Node :=
  if i ≤ 2*g then initialNode else
  let j := i-g
  let lo := trapLower g j l.hl r.hl
  let hi := trapUpper g j l.hh r.hh
  { ll := max p.ll (p.ll+lo-up scale (6*(g : ℤ)^3))
    lh := p.lh+hi
    hl := if i ≤ 3*g then scale else
      p.hl+trapLower g j l.ll r.ll
    hh := if i ≤ 3*g then scale else
      p.hh+trapUpper g j l.lh r.lh+up scale (12*(g : ℤ)^3) }

/-- Reader factorization is definitional equality for the actual Q80 formula. -/
private theorem nodeUpdate_from_three (g i : Nat) (old : Nat → Node) :
    nodeUpdate g i old =
      nodeFromThree g i (old (i - 1)) (old ((i - g) - 1)) (old (i - g)) := by
  rfl

/-- Increasing-index writes preserve every previously completed index.
The proof does not inspect the four integer fields or evaluate any table. -/
private theorem sourceState_completed_index_stable (g completed remaining i : Nat)
    (hi : i ≤ completed) :
    sourceState g (completed + remaining) i = sourceState g completed i := by
  induction remaining with
  | zero => rfl
  | succ remaining ih =>
      have hne : i ≠ completed + remaining + 1 := by omega
      change (if i = completed + remaining + 1 then
        nodeUpdate g (completed + remaining + 1)
          (sourceState g (completed + remaining))
        else sourceState g (completed + remaining) i) = sourceState g completed i
      rw [if_neg hne]
      exact ih

private theorem sourceState_at_completed (g n i : Nat) (hi : i ≤ n) :
    sourceState g n i = sourceState g i i := by
  have h := sourceState_completed_index_stable g i (n - i) i (Nat.le_refl i)
  have hcount : i + (n - i) = n := by omega
  simpa only [hcount] using h

private theorem sourceState_step (g n : Nat) :
    sourceState g (n + 1) (n + 1) = nodeUpdate g (n + 1) (sourceState g n) := by
  change (if n + 1 = n + 1 then nodeUpdate g (n + 1) (sourceState g n)
    else sourceState g n (n + 1)) = _
  rw [if_pos rfl]

/-- Every reader argument is the value at its own completed step.
The positivity assumption is exactly what makes i-g an earlier index. -/
private theorem source_node_recurrence (g n : Nat) (hg : 0 < g) :
    sourceState g (n + 1) (n + 1) =
      nodeFromThree g (n + 1)
        (sourceState g n n)
        (sourceState g (((n + 1) - g) - 1) (((n + 1) - g) - 1))
        (sourceState g ((n + 1) - g) ((n + 1) - g)) := by
  rw [sourceState_step, nodeUpdate_from_three]
  have hp : (n + 1) - 1 = n := by omega
  rw [hp]
  rw [sourceState_at_completed g n (((n + 1) - g) - 1) (by omega)]
  rw [sourceState_at_completed g n ((n + 1) - g) (by omega)]

/-- Supply only already proved predecessor values. The right side still is the
original update arithmetic, not an observed value or a table literal. -/
private theorem source_node_from_values (g n : Nat) (hg : 0 < g)
    (p l r : Node)
    (hp : sourceState g n n = p)
    (hl : sourceState g (((n + 1) - g) - 1) (((n + 1) - g) - 1) = l)
    (hr : sourceState g ((n + 1) - g) ((n + 1) - g) = r) :
    sourceState g (n + 1) (n + 1) = nodeFromThree g (n + 1) p l r := by
  rw [source_node_recurrence g n hg, hp, hl, hr]

/-- This is the per-node interface for a fresh proof-producing evaluation:
harithmetic is checked separately and then composed by equality transitivity. -/
private theorem source_node_from_checked_step (g n : Nat) (hg : 0 < g)
    (p l r value : Node)
    (hp : sourceState g n n = p)
    (hl : sourceState g (((n + 1) - g) - 1) (((n + 1) - g) - 1) = l)
    (hr : sourceState g ((n + 1) - g) ((n + 1) - g) = r)
    (harithmetic : nodeFromThree g (n + 1) p l r = value) :
    sourceState g (n + 1) (n + 1) = value :=
  (source_node_from_values g n hg p l r hp hl hr).trans harithmetic

/-- The original constant-prefix branch supplies initial-node facts at every
needed index up to 2*g, including zero. -/
private theorem sourceState_constant_prefix (g b : Nat) :
    b ≤ 2 * g → sourceState g b = fun _ => initialNode := by
  induction b with
  | zero =>
      intro _
      rfl
  | succ b ih =>
      intro hb
      have hprevious := ih (by omega)
      funext i
      change (if i = b + 1 then nodeUpdate g (b + 1) (sourceState g b)
        else sourceState g b i) = initialNode
      by_cases hi : i = b + 1
      · rw [if_pos hi]
        simp only [nodeUpdate, if_pos hb]
      · rw [if_neg hi]
        exact congrFun hprevious i

private theorem sourceNode_initial (g i : Nat) (hi : i ≤ 2 * g) :
    sourceState g i i = initialNode :=
  congrFun (sourceState_constant_prefix g i hi) i

/-- Boundary information for nodes in the intended nonconstant Q80 prefix.
No division-by-two index or unproved reader substitution is involved. -/
private theorem predecessor_indices (g i : Nat) (hg : 0 < g) (hi : 2 * g < i) :
    i - 1 < i ∧ (i - g) - 1 < i ∧ i - g < i ∧
      (i - g) - 1 + 1 = i - g := by
  omega

private theorem q80_grid_positive : 0 < (16384 : Nat) := by decide

/-- A source-form specialization, not a closed numeric computation. -/
private theorem q80_node_from_values (n : Nat) (p l r : Node)
    (hp : sourceState 16384 n n = p)
    (hl : sourceState 16384 (((n + 1) - 16384) - 1) (((n + 1) - 16384) - 1) = l)
    (hr : sourceState 16384 ((n + 1) - 16384) ((n + 1) - 16384) = r) :
    sourceState 16384 (n + 1) (n + 1) =
      nodeFromThree 16384 (n + 1) p l r :=
  source_node_from_values 16384 n q80_grid_positive p l r hp hl hr

/-- Only the node at 10*g is transported to the full original 12*g table.
There is no claim that a shorter complete reader equals the full table. -/
private theorem sourceTable_from_d10 (value : Node)
    (h : sourceState 16384 (10 * 16384) (10 * 16384) = value) :
    sourceTable (10 * 16384) = value :=
  (sourceState_at_completed 16384 (12 * 16384) (10 * 16384) (by decide)).trans h


/-- Transport any completed query in range to the full unchanged source table. -/
private theorem sourceTable_from_node (i : Nat) (value : Node)
    (hi : i ≤ 12 * 16384) (h : sourceState 16384 i i = value) :
    sourceTable i = value :=
  (sourceState_at_completed 16384 (12 * 16384) i hi).trans h

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

/-- Input and proof-batching parameters, never computed table outputs. -/
private def grid : Nat := 16384
private def constantPrefix : Nat := 2 * grid
private def firstIndex : Nat := constantPrefix + 1
private def blockDepth : Nat := 6
private def blockSize : Nat := 2 ^ blockDepth

/-- Temporary expressions used only while constructing checked equalities. -/
private structure NodeValue where
  index : Nat
  value : Expr

private structure NodeCertificate where
  index : Nat
  value : Expr
  proof : Expr

private structure BlockDraft where
  values : Array NodeValue
  proof : Expr

private def sourceNodeExpr (i : Nat) : Expr :=
  mkApp3 (mkConst ``sourceState) (mkNatLit grid) (mkNatLit i) (mkNatLit i)

/-- Recognize only a literal or its canonical Nat OfNat wrapper, without reduction. -/
private def isNatNormalForm (e : Expr) : Bool :=
  match e with
  | .lit (.natVal _) => true
  | .app (.app (.app (.const ofNatName _) (.const natName []))
      (.lit (.natVal n))) (.app (.const instName []) (.lit (.natVal m))) =>
      ofNatName == ``OfNat.ofNat && natName == ``Nat &&
        instName == ``instOfNatNat && n == m
  | _ => false

/-- Accept both Sym integer literals and exact Int constructors on recognized Nat values.
This checks syntax only; the cbv value and its equality proof are never rewritten. -/
private def isIntegerNormalForm (e : Expr) : Bool :=
  (Lean.Meta.Sym.getIntValue? e).isSome ||
    match e with
    | .app (.const ctor []) n =>
        (ctor == ``Int.ofNat || ctor == ``Int.negSucc) && isNatNormalForm n
    | _ => false

private def isNodeNormalForm (e : Expr) : Bool :=
  e.isAppOfArity ``ImbalancedChen.P2HistoricSieveTableSemantics.HistoricNode.mk 4 &&
    e.getAppArgs.all isIntegerNormalForm

/-- Direct offsets into contiguous arrays; there is no prefix scan. -/
private def lookupCertificate (committed working : Array NodeCertificate)
    (start i : Nat) : MetaM NodeCertificate := do
  if i ≤ constantPrefix then
    let hbound ← mkDecideProof (← Meta.mkLe (mkNatLit i) (mkNatLit constantPrefix))
    return ⟨i, mkConst ``initialNode,
      mkApp3 (mkConst ``sourceNode_initial) (mkNatLit grid) (mkNatLit i) hbound⟩
  if start ≤ i then
    let some cert := working[i - start]?
      | throwError "Missing current-block predecessor certificate at index {i}"
    unless cert.index == i do
      throwError "Current-block certificate index mismatch at {i}"
    return cert
  let some cert := committed[i - firstIndex]?
    | throwError "Missing checked predecessor certificate at index {i}"
  unless cert.index == i do
    throwError "Checked certificate index mismatch at {i}"
  return cert

private def evaluateNode (e : Expr) : MetaM (Expr × Expr) := do
  unless !e.hasFVar && !e.hasMVar do
    throwError "Q80 node arithmetic must be closed before cbvEntry"
  let result ← Lean.Meta.Tactic.Cbv.cbvEntry e
  match result with
  | .step value _ _ _ =>
      unless isNodeNormalForm value do
        let headName : Option Name := match value.getAppFn with
          | .const name _ => some name
          | _ => none
        let args := value.getAppArgs
        let intValues := args.map fun arg =>
          Id.run (OptionT.run (Lean.Meta.Sym.getIntValue? arg))
        let observed := value.consumeMData
        let observedHeadName : Option Name := match observed.getAppFn with
          | .const name _ => some name
          | _ => none
        let observedArgs := observed.getAppArgs
        let observedIntValues := observedArgs.map fun arg =>
          Id.run (OptionT.run (Lean.Meta.Sym.getIntValue? arg.consumeMData))
        throwError "cbvEntry did not return an original HistoricNode four-Int normal form\n\
          raw_value_expr={reprStr value}\n\
          expected_head={``ImbalancedChen.P2HistoricSieveTableSemantics.HistoricNode.mk}\n\
          raw_head_const={reprStr headName}\n\
          raw_args_size={args.size}\n\
          raw_field_int_values={reprStr intValues}\n\
          observed_consumeMData_expr={reprStr observed}\n\
          observed_head_const={reprStr observedHeadName}\n\
          observed_args_size={observedArgs.size}\n\
          observed_field_int_values={reprStr observedIntValues}"
      -- Compact-term experiment: retain the freshly evaluated value only.
      -- Eq.trans still requires arithmetic = value, so the whole-block
      -- synchronous kernel check must validate this conversion.
      return (value, ← mkEqRefl value)
  | .rfl _ _ =>
      throwError "cbvEntry made no progress on the Q80 node arithmetic formula"

/-- Direct Nat.rec avoids compiler-generated partial recursion declarations. -/
private def balancedFold (leaf : Nat → MetaM Expr)
    (combine : Expr → Expr → MetaM Expr) : Nat → Nat → MetaM Expr :=
  Nat.rec (motive := fun _ => Nat → MetaM Expr)
    leaf
    (fun depth next offset => do
      let left ← next offset
      let right ← next (offset + 2 ^ depth)
      combine left right)

private def blockFactType (values : Array NodeValue) : MetaM Expr := do
  unless values.size == blockSize do
    throwError "A Q80 block must contain exactly {blockSize} node facts"
  let facts ← values.mapM fun item => mkEq (sourceNodeExpr item.index) item.value
  balancedFold
    (fun offset => do
      let some fact := facts[offset]? | throwError "Missing block proposition at offset {offset}"
      return fact)
    (fun left right => pure (mkApp2 (mkConst ``And) left right)) blockDepth 0

private def blockFactProof (facts : Array NodeCertificate) : MetaM Expr := do
  unless facts.size == blockSize do
    throwError "A Q80 block proof must contain exactly {blockSize} node facts"
  balancedFold
    (fun offset => do
      let some fact := facts[offset]? | throwError "Missing block proof at offset {offset}"
      return fact.proof)
    (fun left right => mkAppM ``And.intro #[left, right]) blockDepth 0

private def draftBlock (committed : Array NodeCertificate) (start : Nat) :
    (remaining : Nat) → Array NodeCertificate → Array Expr → MetaM BlockDraft :=
  Nat.rec (motive := fun _ => Array NodeCertificate → Array Expr → MetaM BlockDraft)
    (fun working proofLets => do
      let proof ← blockFactProof working
      let proof ← mkLetFVars proofLets proof
        (usedLetOnly := false) (generalizeNondepLet := false)
      let values := working.map fun cert =>
        ({ index := cert.index, value := cert.value } : NodeValue)
      return ⟨values, proof⟩)
    (fun _ next working proofLets => do
      let i := start + working.size
      let p ← lookupCertificate committed working start (i - 1)
      let l ← lookupCertificate committed working start ((i - grid) - 1)
      let r ← lookupCertificate committed working start (i - grid)
      let arithmetic := mkApp5 (mkConst ``nodeFromThree)
        (mkNatLit grid) (mkNatLit i) p.value l.value r.value
      let (value, arithmeticProof) ← evaluateNode arithmetic
      let sourceProof := mkAppN (mkConst ``source_node_from_values)
        #[mkNatLit grid, mkNatLit (i - 1), mkConst ``q80_grid_positive,
          p.value, l.value, r.value, p.proof, l.proof, r.proof]
      let proof := mkApp6 (mkConst ``Eq.trans [.succ .zero]) (mkConst ``Node)
        (sourceNodeExpr i) arithmetic value sourceProof arithmeticProof
      let type ← mkEq (sourceNodeExpr i) value
      withLetDecl (Name.mkSimple s!"q80_node_fact_{i}") type proof fun h =>
        next (working.push ⟨i, value, h⟩) (proofLets.push h))

/-- Select a leaf in the balanced conjunction with logarithmic proof depth. -/
private def projectBalanced : Nat → Expr → Nat → MetaM Expr :=
  Nat.rec (motive := fun _ => Expr → Nat → MetaM Expr)
    (fun proof offset => do
      unless offset == 0 do
        throwError "Invalid balanced-block projection offset"
      return proof)
    (fun depth next proof offset => do
      let half := 2 ^ depth
      if offset < half then
        let left ← mkAppM ``And.left #[proof]
        next left offset
      else
        let right ← mkAppM ``And.right #[proof]
        next right (offset - half))

/-- Only synchronously accepted block facts enter the committed cache. -/
private def checkBlock (committed : Array NodeCertificate) (start : Nat) :
    MetaM (Array NodeCertificate × Name) := do
  unless start == firstIndex + committed.size do
    throwError "The next Q80 block is not contiguous with the checked cache"
  let saved ← Meta.saveState
  tryCatchRuntimeEx
    (do
      let draft ← draftBlock committed start blockSize #[] #[]
      let type ← blockFactType draft.values
      unless !type.hasFVar && !type.hasMVar && !draft.proof.hasFVar && !draft.proof.hasMVar do
        throwError "Q80 block theorem type or proof is not closed"
      let env ← getEnv
      if env.hasUnsafe type || env.hasUnsafe draft.proof then
        throwError "Refusing to submit an unsafe Q80 block theorem"
      let blockName ← withOptions (Elab.async.set · false) do
        mkAuxLemma [] type draft.proof (kind? := some `_q80NodeProofBlock)
      let info ← getConstInfo blockName
      unless isPrivateName blockName do
        throwError "Generated Q80 block theorem is not private"
      match info with
      | .thmInfo _ => pure ()
      | _ => throwError "Generated Q80 block is not a theorem declaration"
      if info.isUnsafe || info.isPartial || info.isAxiom then
        throwError "Generated Q80 block failed the declaration-safety boundary"
      let mut updated := committed
      for offset in [:blockSize] do
        let some item := draft.values[offset]?
          | throwError "Missing checked Q80 value at offset {offset}"
        let proof ← projectBalanced blockDepth (mkConst blockName) offset
        updated := updated.push ⟨item.index, item.value, proof⟩
      logInfo m!"P24_Q80_CHECKED_BLOCK name={blockName} start={start} count={blockSize}"
      return (updated, blockName))
    (fun ex => do
      saved.restore
      throw ex)

/-- Parameterized prefix generation; this diagnostic invokes it for two blocks only. -/
private def buildPrefixBlocks (count : Nat) : MetaM (Array NodeCertificate × Array Name) := do
  unless count * blockSize ≤ 8 * grid do
    throwError "Requested Q80 proof blocks exceed the d10 prefix"
  let mut committed : Array NodeCertificate := #[]
  let mut names : Array Name := #[]
  for block in [:count] do
    unless committed.size == block * blockSize do
      throwError "Checked Q80 cache size is not the expected contiguous prefix"
    let start := firstIndex + committed.size
    let (updated, name) ← checkBlock committed start
    committed := updated
    names := names.push name
  return (committed, names)

/-- Return a terminal sourceTable equality; never put this different proof type
back into the source-node cache. The value remains a temporary Expr. -/
private def makeSourceTableCertificate (committed : Array NodeCertificate)
    (query : Nat) : MetaM (Expr × Expr) := do
  let cert ← lookupCertificate committed #[] (firstIndex + committed.size) query
  let hi ← mkDecideProof (← Meta.mkLe (mkNatLit query) (mkNatLit (12 * grid)))
  let proof := mkAppN (mkConst ``sourceTable_from_node)
    #[mkNatLit query, cert.value, hi, cert.proof]
  return (cert.value, proof)

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

/-- Keep all generated blocks and the final arithmetic theorem under the
private form of the current public declaration prefix, in one naming scope. -/
private def proveArchivedTotal : TacticM Unit := withMainContext do
  let currentPrefix := (← getDeclNGen).namePrefix
  let env ← getEnv
  let privatePrefix :=
    if isPrivateName currentPrefix then currentPrefix else mkPrivateName env currentPrefix
  withDeclNameForAuxNaming privatePrefix do
    let (committed, names) ← buildPrefixBlocks 2048
    unless committed.size == 8 * grid && names.size == 2048 do
      throwError "Unexpected complete d10-prefix block inventory"
    let (value, sourceProof) ← makeSourceTableCertificate committed (10 * grid)
    finishFromSourceNode value sourceProof
    logInfo m!"P24_Q80_ARCHIVED_DONE checked_blocks={names.size} computed_nodes={committed.size} query_index={10 * grid}"

end NodeStepProof

/-- Original archived whole upper endpoint, distinct from the stop target. -/
def archivedOriginalUpper : ℚ :=
  1230679674488580033396846301 / 180734410032387061618573312

set_option maxRecDepth 0 in
set_option maxHeartbeats 0 in
/-- Closed source equality candidate. The private node certificates and
generic formula transport preserve the original computation; the remaining
closed equality is checked by the kernel, without numerical substitutes. -/
theorem cached_fixed_plus_original_compact_eq_archived_candidate :
    fastFixedUpper +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
      archivedOriginalUpper := by
  run_tac NodeStepProof.proveArchivedTotal

/-- Symbolic exact cache transport; neither table implementation is reduced
to prove this transfer. The closed finite equality remains a dependency. -/
theorem original_fixed_plus_original_compact_eq_archived_candidate :
    fixedUpper +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
      archivedOriginalUpper := by
  rw [← fastFixedUpper_eq]
  exact cached_fixed_plus_original_compact_eq_archived_candidate

end ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly

