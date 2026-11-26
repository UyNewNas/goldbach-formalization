/- SOURCE ONLY / UNCOMPILED. Cell01 instance of the unchanged thin proof pattern. -/
import ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge
import ImbalancedChen.P2Saving16CanonicalCell01Binding
import ImbalancedChen.P2Saving16Cell01SegmentedParse

/-!
The unchanged original string parser returns the exact complete cell01 JSON
value. This composes the checked canonical text binding and the checked
reader certificate; it makes no claim about the typed decoder or Q96 guards.
-/
namespace ImbalancedChen.P2Saving16Cell01OriginalJson

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (originalText)
open P2Saving16CanonicalCell01Binding (chars01)
open P2Saving16CanonicalCell01Binding (ofList_chars01_eq_originalText1)
open P2Saving16Cell01Segments (rootValue chars01_length cell01_value532)

theorem cell01_original_json :
    SourceJson.parse (originalText (1 : Fin 14)) = .ok rootValue := by
  apply SourceJson.parse_of_value_of_ofList_eq
    (originalText (1 : Fin 14)) chars01 532 rootValue ['\r', '\n']
    ofList_chars01_eq_originalText1
  · rw [chars01_length]
    decide
  · exact cell01_value532
  · rfl

#print axioms cell01_original_json

end ImbalancedChen.P2Saving16Cell01OriginalJson
