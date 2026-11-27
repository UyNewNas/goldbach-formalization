import ImbalancedChen.P2OriginalSaving16ArchiveCompose
import ImbalancedChen.P2Saving16Cell01OriginalJson
import ImbalancedChen.P2Saving16Cell01Decoded

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell01 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell01OriginalParse
open P2OriginalSaving16OriginalArchive (parsedCell parsedCellSuccess archive)
open P2OriginalSaving16ArchiveCompose
open P2Saving16Cell01Segments (rootValue)
open P2Saving16Cell01OriginalJson (cell01_original_json)
open P2Saving16Cell01Decoded (decodedCell01 cell01_decode)

theorem cell01_original_decode :
    parsedCell (1 : Fin 14) = .ok decodedCell01 := by
  exact parsedCell_of_parse_decode (1 : Fin 14) rootValue decodedCell01
    cell01_original_json cell01_decode

theorem cell01_original_parse_success :
    parsedCellSuccess (1 : Fin 14) = true := by
  exact parsedCellSuccess_of_parsedCell (1 : Fin 14) decodedCell01
    cell01_original_decode

theorem cell01_original_archive : archive (1 : Fin 14) = decodedCell01 := by
  exact archive_of_parsedCell (1 : Fin 14) decodedCell01 cell01_original_decode

#print axioms cell01_original_decode
#print axioms cell01_original_parse_success
#print axioms cell01_original_archive

end ImbalancedChen.P2Saving16Cell01OriginalParse
