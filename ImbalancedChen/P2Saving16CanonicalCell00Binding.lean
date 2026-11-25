import ImbalancedChen.P2OriginalSaving16OriginalInput
import ImbalancedChen.P2Saving16StringCharBinding00

/-!
SOURCE ONLY / NOT COMPILED. Canonical cell00 input binding only.

The imported raw String/Char equality is the already accepted attempt003
statement. This module does not read a file, quote new data, or prove that
53,305-character equality again. The first theorem compares the cell00
String literal selected by the unchanged canonical originalText definition
with the unchanged oldString00 literal. The second only composes equalities.

OriginalInput still needs its current source/input/object-bound acceptance.
This candidate proves no parse, decode, Q96, geometry, or integral result.
-/
namespace ImbalancedChen.P2Saving16CanonicalCell00Binding

open P2OriginalSaving16OriginalArchive (originalText)
open P2Saving16StringCharBinding00 (chars00 oldString00 originalStringeq00)

theorem canonicalText0_eq_oldString00 :
    originalText (0 : Fin 14) = oldString00 := by
  rfl

theorem ofList_chars00_eq_canonicalText0 :
    String.ofList chars00 = originalText (0 : Fin 14) :=
  originalStringeq00.trans canonicalText0_eq_oldString00.symm

#print axioms canonicalText0_eq_oldString00
#print axioms ofList_chars00_eq_canonicalText0

end ImbalancedChen.P2Saving16CanonicalCell00Binding
