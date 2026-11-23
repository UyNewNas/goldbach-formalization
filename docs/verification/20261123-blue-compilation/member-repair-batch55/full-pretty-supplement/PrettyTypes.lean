import ImbalancedChen.P4AOriginalSixthLaterLiteral
import Lean
set_option pp.all true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let requested : Array String := #["_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell0.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell1.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell10.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell11.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell12.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell13.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell14.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell15.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell16.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell17.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell18.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell2.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell3.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell4.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell5.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell6.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell7.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell8.eq_1", "_private.ImbalancedChen.P4AOriginalSixthLaterLiteral.0.ImbalancedChen.P4AOriginalSixthLaterLiteral.rowsCell9.eq_1"]
  let names := env.constants.fold (init := #[]) fun xs n _ =>
    if requested.contains n.toString then xs.push n else xs
  unless names.size == requested.size do throwError "Incomplete exact-name pretty supplement"
  let moduleNames := env.header.moduleNames
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing exact declaration {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    let type ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    let record := Json.mkObj [("name", toJson name.toString),
      ("module", toJson moduleNames[idx.toNat]!.toString),
      ("type", toJson type), ("type_expression", toJson (reprStr info.type)),
      ("universe_parameters", toJson (info.levelParams.map Name.toString))]
    liftIO <| IO.println s!"FULL_PRETTY_TYPE {record.compress}"
