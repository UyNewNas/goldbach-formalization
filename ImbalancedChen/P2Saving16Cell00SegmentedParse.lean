import ImbalancedChen.P2Saving16Cell00DirectParse

/-!
Thin original-fuel consumer of the exact complete cell00 AST equality.
The direct certificate is imported unchanged; it is not reduced again here.
The character count and fuel extension retain the original length-plus-one
reader call. Typed decoding and canonical originalText binding are separate.
-/
namespace ImbalancedChen.P2Saving16Cell00Segments

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2Saving16StringCharBinding00 (chars00)

theorem chars00_length : chars00.length = 53305 := by
  rfl

theorem cell00_value :
    SourceJson.value 53306 chars00 = .ok (rootValue, ['\r', '\n']) :=
  SourceJson.value_success_of_le (by decide : 371 ≤ 53306)
    chars00 (rootValue, ['\r', '\n']) cell00_value371

#print axioms chars00_length
#print axioms cell00_value

end ImbalancedChen.P2Saving16Cell00Segments
