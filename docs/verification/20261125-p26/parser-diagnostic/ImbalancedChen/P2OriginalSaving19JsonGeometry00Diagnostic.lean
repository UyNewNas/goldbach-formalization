import ImbalancedChen.P2OriginalSaving19SourceJson

/-!
DIAGNOSTIC ONLY: exact original cell 00 text, pure SourceJson parser success.
No typed Geometry/Moments decoder, row checker, producer or host JSON parser
is used. The original moment text is loaded but is not a proved parse target.
The source reader is copied byte-for-byte at its recorded SHA256.
-/
namespace ImbalancedChen.P2OriginalSaving19JsonGeometry00Diagnostic

set_option maxRecDepth 1000000

open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)

elab "originalSaving19Geometry00Text%" : term => do
  let s ← IO.FS.readFile
    "/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json"
  elabTerm (Syntax.mkStrLit s) (some (mkConst ``String))

elab "originalSaving19Moment00Text%" : term => do
  let s ← IO.FS.readFile
    "/workspace/goldbach-research/eighth-third-moment-refinement-20261009-a23-low-00.witness.json"
  elabTerm (Syntax.mkStrLit s) (some (mkConst ``String))

def geometry00Text : String := originalSaving19Geometry00Text%
def moment00Text : String := originalSaving19Moment00Text%

theorem geometry00_json_parse_success :
    (SourceJson.parse geometry00Text).toOption.isSome = true := by
  decide +kernel

#print axioms geometry00_json_parse_success

end ImbalancedChen.P2OriginalSaving19JsonGeometry00Diagnostic
