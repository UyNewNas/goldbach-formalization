/- SOURCE ONLY / UNCOMPILED. Cell01 instance of the unchanged thin proof pattern. -/
import ImbalancedChen.P2Saving16Cell01DirectParse

/-!
Thin original-fuel consumer of the exact complete cell01 AST equality.
The direct certificate is imported unchanged; it is not reduced again here.
The character count and fuel extension retain the original length-plus-one
reader call. Typed decoding and canonical originalText binding are separate.
-/
namespace ImbalancedChen.P2Saving16Cell01Segments

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2Saving16CanonicalCell01Binding (chars01)

theorem chars01_length : chars01.length = 344873 := by
  rfl

theorem cell01_value :
    SourceJson.value 344874 chars01 = .ok (rootValue, ['\r', '\n']) :=
  SourceJson.value_success_of_le (by decide : 532 ≤ 344874)
    chars01 (rootValue, ['\r', '\n']) cell01_value532

#print axioms chars01_length
#print axioms cell01_value

end ImbalancedChen.P2Saving16Cell01Segments
