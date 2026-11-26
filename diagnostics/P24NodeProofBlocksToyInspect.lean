import «p24-node-proof-blocks-toy-20261126».«attempt-001».Toy
import Lean
import Lean.Meta.Sym.LitValues

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName := `«p24-node-proof-blocks-toy-20261126».«attempt-001».Toy
  let some owner := env.getModuleIdx? moduleName
    | throwError "Missing toy module"
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>
    if i == owner && (env.find? n).isSome then ns.push n else ns
  let sourceNames := names.filter fun n =>
    privateToUserName n == `P24NodeProofBlocksToy.sourceState
  let nodeNames := names.filter fun n =>
    privateToUserName n == `P24NodeProofBlocksToy.Node
  let ctorNames := names.filter fun n =>
    privateToUserName n == `P24NodeProofBlocksToy.Node.mk
  unless sourceNames.size == 1 && nodeNames.size == 1 && ctorNames.size == 1 do
    throwError "Cannot uniquely resolve the original toy sourceState/Node constructors"
  let sourceName := sourceNames[0]!
  let nodeName := nodeNames[0]!
  let ctorName := ctorNames[0]!
  let blocks := (names.filter fun n =>
    n.anyS (fun part => "_nodeProofBlock".isPrefixOf part)).qsort Name.lt
  let asNat? : Expr → Option Nat := fun e =>
    match e.consumeMData with
    | .lit (.natVal n) => some n
    | e => Lean.Meta.Sym.getNatValue? e
  let mut allOK := blocks.size == 2
  let mut allIndices : Array Nat := #[]
  let mut totalTypeNodes := 0
  for name in blocks do
    let some info := env.find? name
      | throwError "Missing generated block"
    let isTheorem := match info with
      | .thmInfo _ => true
      | _ => false
    let type := info.type.consumeMData
    let mut facts : Array Expr := #[]
    if type.isAppOfArity ``And 2 then
      let pair := type.getAppArgs
      let left := pair[0]!.consumeMData
      let right := pair[1]!.consumeMData
      if left.isAppOfArity ``And 2 && right.isAppOfArity ``And 2 then
        let lhs := left.getAppArgs
        let rhs := right.getAppArgs
        facts := #[lhs[0]!, lhs[1]!, rhs[0]!, rhs[1]!]
    let mut blockOK := isPrivateName name && isTheorem &&
      !info.isUnsafe && !info.isPartial && !info.isAxiom &&
      !type.hasFVar && !type.hasMVar && facts.size == 4
    let mut indices : Array Nat := #[]
    let mut factRecords : Array Json := #[]
    for originalFact in facts do
      let fact := originalFact.consumeMData
      let mut factOK := false
      let mut index : Option Nat := none
      let mut grid : Option Nat := none
      let mut completed : Option Nat := none
      let mut values : Array (Option Int) := #[]
      if fact.isAppOfArity ``Eq 3 then
        let equality := fact.getAppArgs
        let lhs := equality[1]!.consumeMData
        let rhs := equality[2]!.consumeMData
        if equality[0]!.isConstOf nodeName &&
            lhs.isAppOfArity sourceName 3 && rhs.isAppOfArity ctorName 4 then
          let sourceArgs := lhs.getAppArgs
          grid := asNat? sourceArgs[0]!
          completed := asNat? sourceArgs[1]!
          index := asNat? sourceArgs[2]!
          values := rhs.getAppArgs.map Lean.Meta.Sym.getIntValue?
          factOK := grid == some 2 && index.isSome &&
            completed == index && values.all Option.isSome
      if let some i := index then indices := indices.push i
      blockOK := blockOK && factOK
      factRecords := factRecords.push <| Json.mkObj [
        ("grid", toJson grid), ("completed", toJson completed),
        ("index", toJson index), ("four_int_normal_form", toJson values),
        ("exact_source_node_equality", toJson factOK)]
    blockOK := blockOK &&
      (indices == #[5, 6, 7, 8] || indices == #[9, 10, 11, 12])
    allOK := allOK && blockOK
    allIndices := allIndices ++ indices
    let nodes := info.type.sizeWithoutSharing
    totalTypeNodes := totalTypeNodes + nodes
    let record := Json.mkObj [
      ("name", toJson name.toString), ("private", toJson (isPrivateName name)),
      ("theorem", toJson isTheorem), ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom),
      ("four_fact_balanced_and", toJson (facts.size == 4)),
      ("indices", toJson indices), ("facts", toJson factRecords),
      ("type_expr_nodes_without_sharing", toJson nodes),
      ("shape_checks_passed", toJson blockOK)]
    liftIO <| IO.println s!"P24_TOY_BLOCK {record.compress}"
  allOK := allOK &&
    allIndices.qsort (· < ·) == #[5, 6, 7, 8, 9, 10, 11, 12]
  let summary := Json.mkObj [
    ("module", toJson moduleName.toString), ("diagnostic_only", toJson true),
    ("owned_block_count", toJson blocks.size),
    ("total_type_expr_nodes_without_sharing", toJson totalTypeNodes),
    ("indices", toJson allIndices), ("shape_checks_passed", toJson allOK),
    ("P2_acceptance_credit", toJson false)]
  liftIO <| IO.println s!"P24_TOY_BLOCK_SUMMARY {summary.compress}"
  unless allOK do
    throwError "Toy block shape diagnostics failed"
