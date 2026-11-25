import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData01
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData02
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData03
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData04
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData06
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData07
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData08
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData09
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData10
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData11
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData00
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData01
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData02
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData03
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData04
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData05
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData06
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData07
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData08
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData09
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData10
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData11
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData12

/-! SOURCE CANDIDATE, NOT COMPILED. Fin 13 input maps only. Fin.cases gives
exactly thirteen ordered entries and an impossible Fin 0 tail, with no default
cell or dropped source fields. This module performs no file I/O itself. -/
namespace ImbalancedChen.P2OriginalSaving19Archive

noncomputable def geometryPacked : Fin 13 → P2OriginalSaving19PackedChars.Tree :=
  Fin.cases geometryPacked00 (Fin.cases geometryPacked01 (Fin.cases geometryPacked02 (Fin.cases geometryPacked03 (Fin.cases geometryPacked04 (Fin.cases geometryPacked05 (Fin.cases geometryPacked06 (Fin.cases geometryPacked07 (Fin.cases geometryPacked08 (Fin.cases geometryPacked09 (Fin.cases geometryPacked10 (Fin.cases geometryPacked11 (Fin.cases geometryPacked12 (Fin.elim0)))))))))))))

noncomputable def geometryChars (c : Fin 13) : List Char :=
  (geometryPacked c).toList

noncomputable def momentPacked : Fin 13 → P2OriginalSaving19PackedChars.Tree :=
  Fin.cases momentPacked00 (Fin.cases momentPacked01 (Fin.cases momentPacked02 (Fin.cases momentPacked03 (Fin.cases momentPacked04 (Fin.cases momentPacked05 (Fin.cases momentPacked06 (Fin.cases momentPacked07 (Fin.cases momentPacked08 (Fin.cases momentPacked09 (Fin.cases momentPacked10 (Fin.cases momentPacked11 (Fin.cases momentPacked12 (Fin.elim0)))))))))))))

noncomputable def momentChars (c : Fin 13) : List Char :=
  (momentPacked c).toList

end ImbalancedChen.P2OriginalSaving19Archive
