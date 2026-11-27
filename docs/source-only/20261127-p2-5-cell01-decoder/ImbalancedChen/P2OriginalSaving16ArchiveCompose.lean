import ImbalancedChen.P2OriginalSaving16FiniteCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell01 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2OriginalSaving16ArchiveCompose
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
  (originalText decodeCell parsedCell parsedCellSuccess archive)

/- Public extraction of the three already written symbolic transports. -/
theorem parsedCell_of_parse_decode
    (i : Fin 14) (root : SourceJson)
    (decoded : P2OriginalSaving16OriginalArchive.CellRecord)
    (hparse : SourceJson.parse (originalText i) = .ok root)
    (hdecode : decodeCell root = .ok decoded) :
    parsedCell i = .ok decoded := by
  exact (congrArg (fun result : Except String SourceJson => result >>= decodeCell)
    hparse).trans hdecode

theorem parsedCellSuccess_of_parsedCell
    (i : Fin 14) (decoded : P2OriginalSaving16OriginalArchive.CellRecord)
    (hdecode : parsedCell i = .ok decoded) :
    parsedCellSuccess i = true := by
  exact congrArg
    (fun result : Except String P2OriginalSaving16OriginalArchive.CellRecord =>
      match result with | .ok _ => true | .error _ => false)
    hdecode

theorem archive_of_parsedCell
    (i : Fin 14) (decoded : P2OriginalSaving16OriginalArchive.CellRecord)
    (hdecode : parsedCell i = .ok decoded) :
    archive i = decoded := by
  exact congrArg
    (fun result : Except String P2OriginalSaving16OriginalArchive.CellRecord =>
      result.toOption.getD default)
    hdecode

end ImbalancedChen.P2OriginalSaving16ArchiveCompose
