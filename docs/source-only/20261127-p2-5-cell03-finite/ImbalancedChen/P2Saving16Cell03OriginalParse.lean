import ImbalancedChen.P2OriginalSaving16ArchiveCompose
import ImbalancedChen.P2Saving16Cell03OriginalJson
import ImbalancedChen.P2Saving16Cell03Decoded

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell03 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell03OriginalParse
open P2OriginalSaving16OriginalArchive (parsedCell parsedCellSuccess archive)
open P2OriginalSaving16ArchiveCompose
open P2Saving16Cell03Segments (rootValue)
open P2Saving16Cell03OriginalJson (cell03_original_json)
open P2Saving16Cell03Decoded (decodedCell03 cell03_decode)

theorem cell03_original_decode :
    parsedCell (3 : Fin 14) = .ok decodedCell03 := by
  exact parsedCell_of_parse_decode (3 : Fin 14) rootValue decodedCell03
    cell03_original_json cell03_decode

theorem cell03_original_parse_success :
    parsedCellSuccess (3 : Fin 14) = true := by
  exact parsedCellSuccess_of_parsedCell (3 : Fin 14) decodedCell03
    cell03_original_decode

theorem cell03_original_archive : archive (3 : Fin 14) = decodedCell03 := by
  exact archive_of_parsedCell (3 : Fin 14) decodedCell03 cell03_original_decode

#print axioms cell03_original_decode
#print axioms cell03_original_parse_success
#print axioms cell03_original_archive

end ImbalancedChen.P2Saving16Cell03OriginalParse
