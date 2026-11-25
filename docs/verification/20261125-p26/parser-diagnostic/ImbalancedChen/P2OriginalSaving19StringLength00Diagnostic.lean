import Lean

/-!
DIAGNOSTIC ONLY: the same exact original geometry cell 00 String literal.
This closed length equality isolates String/UTF-8/List Char reduction.
There is no SourceJson parser, typed decoder or host mathematical checker.
-/
namespace ImbalancedChen.P2OriginalSaving19StringLength00Diagnostic

set_option maxRecDepth 1000000

open Lean Elab Term

elab "originalSaving19Length00Text%" : term => do
  let s ← IO.FS.readFile
    "/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json"
  elabTerm (Syntax.mkStrLit s) (some (mkConst ``String))

def geometry00Text : String := originalSaving19Length00Text%

#check geometry00Text

theorem geometry00_string_length : geometry00Text.length = 195134 := by
  decide +kernel

#print axioms geometry00_string_length

end ImbalancedChen.P2OriginalSaving19StringLength00Diagnostic
