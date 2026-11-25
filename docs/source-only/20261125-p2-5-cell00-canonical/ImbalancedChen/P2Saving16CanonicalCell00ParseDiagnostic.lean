import ImbalancedChen.P2Saving16CanonicalCell00Binding
import ImbalancedChen.P2OriginalSaving16Decoder
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-!
SOURCE ONLY / NOT COMPILED. Single canonical cell00 parse/decode diagnostic.

The target is the original FiniteArchive parsedCellSuccess at index zero,
with parsedCell and its Bool constructor test expanded inline. The finite
owner and its four closed guards are not imported or modified. The complete
original parse result is bound to the unchanged decodeCell; only the Except
constructor is tested, without equality of CellRecord or raw JSON payloads.

The existing character-input theorem transports this exact bind expression
using the canonical String/Char equality. It retains value, whitespace,
length-plus-one fuel, errors and the complete typed decoder. The remaining
closed Bool target is attempted with the original decide +kernel method.
There is no parse-success premise or imported concrete success theorem.

Compile only after the canonical binding and all dependency objects have
current source-bound replay and complete owned acceptance. This candidate
has not run and provides no Q96, geometry, integral, or whole-family credit.
-/
namespace ImbalancedChen.P2Saving16CanonicalCell00ParseDiagnostic

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (originalText decodeCell)
open P2Saving16StringCharBinding00 (chars00)
open P2Saving16CanonicalCell00Binding (ofList_chars00_eq_canonicalText0)

theorem cell00_parse_success_diagnostic :
    (match (SourceJson.parse (originalText (0 : Fin 14)) >>= decodeCell) with
     | .ok _ => true
     | .error _ => false) = true := by
  rw [SourceJson.parse_bind_eq_parseChars_bind_of_ofList_eq
    decodeCell (originalText (0 : Fin 14)) chars00
    ofList_chars00_eq_canonicalText0]
  decide +kernel

#print axioms cell00_parse_success_diagnostic

end ImbalancedChen.P2Saving16CanonicalCell00ParseDiagnostic
