/- SOURCE ONLY / UNCOMPILED. Cell03 instance of the unchanged thin proof pattern. -/
import ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge
import ImbalancedChen.P2Saving16CanonicalCell03Binding
import ImbalancedChen.P2Saving16Cell03SegmentedParse

/-!
The unchanged original string parser returns the exact complete cell03 JSON
value. This composes the checked canonical text binding and the checked
reader certificate; it makes no claim about the typed decoder or Q96 guards.
-/
namespace ImbalancedChen.P2Saving16Cell03OriginalJson

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (originalText)
open P2Saving16CanonicalCell03Binding (chars03)
open P2Saving16CanonicalCell03Binding (ofList_chars03_eq_originalText3)
open P2Saving16Cell03Segments (rootValue chars03_length cell03_value556)

theorem cell03_original_json :
    SourceJson.parse (originalText (3 : Fin 14)) = .ok rootValue := by
  apply SourceJson.parse_of_value_of_ofList_eq
    (originalText (3 : Fin 14)) chars03 556 rootValue ['\r', '\n']
    ofList_chars03_eq_originalText3
  · rw [chars03_length]
    decide
  · exact cell03_value556
  · rfl

#print axioms cell03_original_json

end ImbalancedChen.P2Saving16Cell03OriginalJson
