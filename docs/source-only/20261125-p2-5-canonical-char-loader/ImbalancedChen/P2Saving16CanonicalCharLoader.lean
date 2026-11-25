import Lean
import ImbalancedChen.P2OriginalSaving16OriginalInput

/-!
SOURCE ONLY / NOT COMPILED. Character quotation from an imported canonical
saving16 String literal. The argument is elaborated at type Fin 14 through
originalText; official Meta reduction must expose an actual String literal.
Only the existing toExpr s.toList quotation is then performed.

This module has no file reader, JSON parser, typed decoder, numerical checker,
or equality proof. A nonliteral reduction result is rejected. Acceptance of
the imported OriginalInput source/input/object binding remains a prerequisite.
-/
namespace ImbalancedChen.P2Saving16CanonicalCharLoader

open Lean Elab Term

elab "canonicalSaving16Chars% " i:term : term => do
  let text ← elabTermAndSynthesize
    (← `(ImbalancedChen.P2OriginalSaving16OriginalArchive.originalText ($i : Fin 14)))
    (some (mkConst ``String))
  let literal ← Meta.withTransparency .all (Meta.whnf text)
  match literal with
  | .lit (.strVal s) => return toExpr s.toList
  | _ => throwError "canonical originalText did not reduce to a String literal"

end ImbalancedChen.P2Saving16CanonicalCharLoader
