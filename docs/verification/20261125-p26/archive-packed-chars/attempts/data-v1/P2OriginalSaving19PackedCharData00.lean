import ImbalancedChen.P2OriginalSaving19PackedChars

/-! Candidate input representation. Only geometry00 is loaded. No parser or
closed equality to the old Core String is asserted. The quotation runs the same
pure pack whose full Unicode/tree round-trip was kernel checked. -/
namespace ImbalancedChen.P2OriginalSaving19PackedChars

open Lean Elab Term
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false

private def quoteTree : Tree → Expr
  | .empty => mkConst ``Tree.empty
  | .leaf n word => mkApp2 (mkConst ``Tree.leaf) (mkNatLit n) (mkNatLit word)
  | .branch l r => mkApp2 (mkConst ``Tree.branch) (quoteTree l) (quoteTree r)

elab "includeGeometryPacked00%" : term => do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 before_readFile"
  err.flush
  let s ← IO.FS.readFile "/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json"
  let chars := s.toList
  err.putStrLn s!"PACKED00 after_readFile codepoints={chars.length}"
  err.flush
  let packed := pack chars
  err.putStrLn s!"PACKED00 after_pack structural_count={packed.count}"
  err.flush
  let result := quoteTree packed
  err.putStrLn "PACKED00 after_quote"
  err.flush
  return result

noncomputable def geometryPacked00 : Tree := includeGeometryPacked00%
noncomputable def geometryPackedChars00 : List Char := geometryPacked00.toList

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 data_definitions_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19PackedChars
