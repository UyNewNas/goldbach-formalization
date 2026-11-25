import ImbalancedChen.P2OriginalSaving16FiniteCore
import ImbalancedChen.P2Saving16Cell00OriginalJson
import ImbalancedChen.P2Saving16Cell00Decoded

/-!
Connect the original cell00 input, exact complete parser result, and unchanged
typed decoder to the existing finite-archive definitions. The four all-cell
finite guards are not imported or replaced. No parsing premise is introduced.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalParse

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
  (originalText decodeCell parsedCell parsedCellSuccess archive)
open P2Saving16Cell00Segments (rootValue)
open P2Saving16Cell00OriginalJson (cell00_original_json)
open P2Saving16Cell00Decoded (decodedCell00 cell00_decode)

theorem cell00_original_decode :
    parsedCell (0 : Fin 14) = .ok decodedCell00 := by
  change (SourceJson.parse (originalText (0 : Fin 14)) >>= decodeCell) = .ok decodedCell00
  rw [cell00_original_json]
  exact cell00_decode

theorem cell00_original_parse_success :
    parsedCellSuccess (0 : Fin 14) = true := by
  unfold parsedCellSuccess
  rw [cell00_original_decode]
  rfl

theorem cell00_original_archive : archive (0 : Fin 14) = decodedCell00 := by
  unfold archive
  rw [cell00_original_decode]
  rfl

#print axioms cell00_original_decode
#print axioms cell00_original_parse_success
#print axioms cell00_original_archive

end ImbalancedChen.P2Saving16Cell00OriginalParse
