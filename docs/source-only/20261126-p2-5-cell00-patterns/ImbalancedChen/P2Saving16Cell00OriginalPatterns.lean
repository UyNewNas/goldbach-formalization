import ImbalancedChen.P2Saving16Cell00OriginalFloors
import ImbalancedChen.P2Saving16Cell00TypedPatterns

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the complete typed cell00 pattern guard through the existing
original-payload equality. The original source index is 0, the value of
`sourceId (atlasCell (0 : Fin 14))` in the existing global owner. This
consumer neither imports that owner's pending global decisions nor
changes the original mask definitions or the 96-row order.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalPatterns

open P2OriginalSaving16OriginalArchive (archive)
open P2Saving16Cell00OriginalFloors (cell00_original_payload)
open P4AOriginalAscending14Literal42 (literalLeftMasks)

theorem cell00_original_patterns :
    (archive (0 : Fin 14)).leftMasks.toList.toFinset = literalLeftMasks (0 : Fin 15) ∧
    Disjoint (archive (0 : Fin 14)).leftMasks.toList.toFinset
      (archive (0 : Fin 14)).rightMasks.toList.toFinset ∧
    (archive (0 : Fin 14)).leftMasks.toList.toFinset ∪
      (archive (0 : Fin 14)).rightMasks.toList.toFinset = Finset.Icc 1 63 ∧
    6 ∈ (archive (0 : Fin 14)).rightMasks.toList.toFinset :=
  cell00_original_payload.symm ▸ P2Saving16Cell00TypedPatterns.cell00_patterns

#print axioms cell00_original_patterns

end ImbalancedChen.P2Saving16Cell00OriginalPatterns
