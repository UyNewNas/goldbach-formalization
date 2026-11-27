/- SOURCE ONLY / UNCOMPILED. Cell03 instance of the unchanged thin proof pattern. -/
import ImbalancedChen.P2Saving16Cell03DirectParse

/-!
Thin original-fuel consumer of the exact complete cell03 AST equality.
The direct certificate is imported unchanged; it is not reduced again here.
The character count and fuel extension retain the original length-plus-one
reader call. Typed decoding and canonical originalText binding are separate.
-/
namespace ImbalancedChen.P2Saving16Cell03Segments

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2Saving16CanonicalCell03Binding (chars03)

theorem chars03_length : chars03.length = 125188 := by
  rfl

theorem cell03_value :
    SourceJson.value 125189 chars03 = .ok (rootValue, ['\r', '\n']) :=
  SourceJson.value_success_of_le (by decide : 556 ≤ 125189)
    chars03 (rootValue, ['\r', '\n']) cell03_value556

#print axioms chars03_length
#print axioms cell03_value

end ImbalancedChen.P2Saving16Cell03Segments
