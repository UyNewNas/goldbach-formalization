import ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge
import ImbalancedChen.P2Saving16CanonicalCell00Binding
import ImbalancedChen.P2Saving16Cell00SegmentedParse

/-!
The unchanged original string parser returns the exact complete cell00 JSON
value. This composes the checked canonical text binding and the checked
reader certificate; it makes no claim about the typed decoder or Q96 guards.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalJson

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (originalText)
open P2Saving16StringCharBinding00 (chars00)
open P2Saving16CanonicalCell00Binding (ofList_chars00_eq_canonicalText0)
open P2Saving16Cell00Segments (rootValue chars00_length cell00_value371)

theorem cell00_original_json :
    SourceJson.parse (originalText (0 : Fin 14)) = .ok rootValue := by
  apply SourceJson.parse_of_value_of_ofList_eq
    (originalText (0 : Fin 14)) chars00 371 rootValue ['\r', '\n']
    ofList_chars00_eq_canonicalText0
  · rw [chars00_length]
    decide
  · exact cell00_value371
  · rfl

#print axioms cell00_original_json

end ImbalancedChen.P2Saving16Cell00OriginalJson
