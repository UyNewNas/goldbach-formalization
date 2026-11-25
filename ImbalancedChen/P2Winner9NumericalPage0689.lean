import ImbalancedChen.P2Winner9CompleteSeedBlock43
import ImbalancedChen.P2Winner9SelectedArchiveChecker
import ImbalancedChen.P2Winner9SeedArchiveChecks
import ImbalancedChen.P2Winner9MaterializedLogChecker

/-! Original selected numerical certificates for ordinals 11024–11025. -/

namespace ImbalancedChen.P2Winner9NumericalPage0689
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)
open P2Winner9MaterializedLogChecker (checkSelectedMaterialized_sound)

set_option maxRecDepth 50000
set_option maxHeartbeats 40000000
set_option Elab.async true

private theorem row00 : checkSelected (P2Winner9CompleteSeedBlock43.pages[1]!)[0]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row01 : checkSelected (P2Winner9CompleteSeedBlock43.pages[1]!)[1]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

theorem checked : Checked (fun _ r => checkSelected r = true) 11024 2
    (P2Winner9CompleteSeedBlock43.pages[1]!) := by
  refine ⟨by decide +kernel, fun i => ?_⟩
  fin_cases i
  · exact row00
  · exact row01

end ImbalancedChen.P2Winner9NumericalPage0689
