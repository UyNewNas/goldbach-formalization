import ImbalancedChen.P2OriginalSaving16FiniteCore
import ImbalancedChen.P2Saving16Cell00OriginalJson
import ImbalancedChen.P2Saving16Cell00Decoded

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Transport the existing original JSON and typed decoder certificates through
the unchanged finite-archive definitions. Three private wrappers perform the
definitional conversions at a symbolic cell index and payload; the closed
theorems only instantiate these wrappers. The three public statements and
imports are unchanged. No parser, decoder, input, payload, finite guard, or
new premise is introduced. The complete owned audit must include all three
private wrappers and every generated declaration.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalParse

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
  (originalText decodeCell parsedCell parsedCellSuccess archive)
open P2Saving16Cell00Segments (rootValue)
open P2Saving16Cell00OriginalJson (cell00_original_json)
open P2Saving16Cell00Decoded (decodedCell00 cell00_decode)

/- A variable index prevents reduction from choosing any of the fourteen
original text literals. The closed public applications below have exactly
the named FiniteCore heads in these conclusions, so they do not repeat the
parse/bind or projection conversions at index zero. -/
private theorem parsedCell_of_parse_decode
    (i : Fin 14) (root : SourceJson)
    (decoded : P2OriginalSaving16OriginalArchive.CellRecord)
    (hparse : SourceJson.parse (originalText i) = .ok root)
    (hdecode : decodeCell root = .ok decoded) :
    parsedCell i = .ok decoded := by
  exact (congrArg (fun result : Except String SourceJson => result >>= decodeCell)
    hparse).trans hdecode

private theorem parsedCellSuccess_of_parsedCell
    (i : Fin 14) (decoded : P2OriginalSaving16OriginalArchive.CellRecord)
    (hdecode : parsedCell i = .ok decoded) :
    parsedCellSuccess i = true := by
  exact congrArg
    (fun result : Except String P2OriginalSaving16OriginalArchive.CellRecord =>
      match result with | .ok _ => true | .error _ => false)
    hdecode

private theorem archive_of_parsedCell
    (i : Fin 14) (decoded : P2OriginalSaving16OriginalArchive.CellRecord)
    (hdecode : parsedCell i = .ok decoded) :
    archive i = decoded := by
  exact congrArg
    (fun result : Except String P2OriginalSaving16OriginalArchive.CellRecord =>
      result.toOption.getD default)
    hdecode

theorem cell00_original_decode :
    parsedCell (0 : Fin 14) = .ok decodedCell00 := by
  exact parsedCell_of_parse_decode (0 : Fin 14) rootValue decodedCell00
    cell00_original_json cell00_decode

theorem cell00_original_parse_success :
    parsedCellSuccess (0 : Fin 14) = true := by
  exact parsedCellSuccess_of_parsedCell (0 : Fin 14) decodedCell00
    cell00_original_decode

theorem cell00_original_archive : archive (0 : Fin 14) = decodedCell00 := by
  exact archive_of_parsedCell (0 : Fin 14) decodedCell00 cell00_original_decode

#print axioms cell00_original_decode
#print axioms cell00_original_parse_success
#print axioms cell00_original_archive

end ImbalancedChen.P2Saving16Cell00OriginalParse
