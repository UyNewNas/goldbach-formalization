import ImbalancedChen.P2OriginalSaving19ArchiveCore

/-!
DIAGNOSTIC CANDIDATE ONLY / NOT COMPILED.

Two closed pure parse checks for original cell 00. The imported Core keeps
all original loaders and all thirteen entries of each text dictionary;
only these two proof goals are restricted to cell 00. No original data,
parser implementation or typed fallback definition has been changed.
This module does not assert the full Archive guards or any other cell.
-/
namespace ImbalancedChen.P2OriginalSaving19ArchiveParse00

set_option maxRecDepth 1000000

open P2OriginalSaving19Archive

theorem geometry_parse_00 :
    geometryParse (0 : Fin 13) = .ok (geometry 0) := by decide

theorem moment_parse_00 :
    momentParse (0 : Fin 13) = .ok (moments 0) := by decide

#print axioms geometry_parse_00
#print axioms moment_parse_00

end ImbalancedChen.P2OriginalSaving19ArchiveParse00
