import ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex

/-!
SOURCE ONLY / NOT COMPILED OR KERNEL ACCEPTED.
Mechanical movement of the original archived rational-value accessor.
This core supplies no inequality for any of the other 86 cell integrals.
Before loading the former ArchivedIntegralRows owner with the selected seed
supplier, remove its moved declaration and import this core.
-/

namespace ImbalancedChen.P4AOriginalFull87ArchivedIntegralRows
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ArchiveSourceIndex (archivedRecordForOriginalCell)

def archived (c : Cell) : ℚ := (archivedRecordForOriginalCell c).2

end
end ImbalancedChen.P4AOriginalFull87ArchivedIntegralRows
